-- Prove2me | Theorems.Thm_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ
-- name    : CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/b0a5b75b-8253-56c3-8b51-f397ea744fe1
-- title:
--   Affine descent criterion for corepresentability of a functor
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a functor from the category of commutative rings under $\mathrm{CommRingCat.of}\ R$ (that is, of commutative $R$-algebras) to sets in an arbitrary universe. Assume the descent condition: for every morphism $\varphi : B \to B'$ of $R$-algebras whose underlying ring map is flat and whose induced map $\operatorname{Spec} B' \to \operatorname{Spec} B$ on prime spectra is surjective, the map $F(\varphi)$ is injective, and every $y \in F(B')$ equalised by the images of the two pushout inclusions $B' \to B' \otimes_B B'$ lies in the image of $F(\varphi)$. Let $S_1$ be an $R$-algebra that is faithfully flat as an $R$-module, and let $C_1$ be a commutative ring that is an $R$-algebra and an $S_1$-algebra compatibly. Assume given, for every $R$-algebra $B$ and every $R$-algebra map $j : S_1 \to B$, a bijection $e_{B,j}$ from $F(B)$ onto the set of $R$-algebra maps $g : C_1 \to B$ with $g \circ (S_1 \to C_1) = j$, natural in the sense that for every $R$-algebra map $\psi : B \to B'$ and every $x \in F(B)$ one has $e_{B',\psi \circ j}(F(\psi)x) = \psi \circ e_{B,j}(x)$. Assume further an $R$-algebra isomorphism $\varphi : C_1 \otimes_R S_1 \xrightarrow{\sim} S_1 \otimes_R C_1$ such that for every $R$-algebra $D$, every $R$-algebra map $d : S_1 \otimes_R S_1 \to D$ and every $x \in F(D)$, the map $C_1 \otimes_R S_1 \to D$ determined by $e_{D,\,d \circ \mathrm{includeLeft}}(x)$ on $C_1$ and $d \circ \mathrm{includeRight}$ on $S_1$ agrees with the precomposition by $\varphi$ of the map $S_1 \otimes_R C_1 \to D$ determined by $d \circ \mathrm{includeLeft}$ on $S_1$ and $e_{D,\,d \circ \mathrm{includeRight}}(x)$ on $C_1$. Finally, writing $C \subseteq C_1$ for the equaliser subalgebra of the two maps $C_1 \to S_1 \otimes_R C_1$ given by $a \mapsto \varphi(a \otimes 1)$ and $a \mapsto 1 \otimes a$, assume that the induced $R$-algebra map $S_1 \otimes_R C \to C_1$ (the lift of the structure map $S_1 \to C_1$ and the inclusion $C \hookrightarrow C_1$) is bijective. Then there exists an $R$-algebra $C$ such that $F$ is corepresentable by it, i.e. $F$ admits a `CorepresentableBy` datum at some object of $\mathrm{Under}(\mathrm{CommRingCat.of}\ R)$.
--
--   This is the affine form of fpqc descent for corepresentability: a functor on $R$-algebras satisfying descent along flat maps that are surjective on spectra, and corepresentable after the faithfully flat base change $R \to S_1$ by an algebra $C_1$ carrying a descent datum $\varphi$ whose descended algebra recovers $C_1$ after base change, is corepresentable over $R$ itself. It is the assembly step used by [`CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ`](thm.html#CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ), and the element-level descent it relies on is [`Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul`](thm.html#Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

theorem CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁)
      (AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
        (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)).val (fun s a => Commute.all _ _))) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C) := by sorry
