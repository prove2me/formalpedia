-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_fibrePower_homScheme_of_naturalOperation
-- name    : AlgebraicGeometry.exists_hom_fibrePower_homScheme_of_naturalOperation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3f51720b-f7af-5279-adf2-d323e548b818
-- title:
--   Natural operations induced on fibre powers of a Hom-scheme
-- statement:
--   Let $R$ be a commutative ring, $f : A \to \operatorname{Spec} R$ a morphism of schemes carrying a relative group law $L$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} R$, compatible with precomposition), and let $\pi_H : H \to \operatorname{Spec} R$ be equipped with a rule $\mathrm{pt}$ assigning to every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and every $\varphi : A \times_{\operatorname{Spec} R} \operatorname{Spec} S' \to A$ with $\varphi \circ f = s \circ \mathrm{pr}_2$ a morphism $\operatorname{Spec} S' \to H$ over $s$. Call $\varphi$ multiplicative if for all $T$, all $t' : T \to \operatorname{Spec} S'$ and all $P,Q$ over $t' \circ s$, composing $\varphi$ with the lift of $(L.\mathrm{mul}(P,Q), t')$ gives $L.\mathrm{mul}$ of the composites of the lifts of $(P,t')$ and $(Q,t')$ with $\varphi$. Assume: $\mathrm{pt}$ is natural in $\psi : S' \to S''$ (`hHnat`); every point of $H$ over $s$ is $\mathrm{pt}(\varphi)$ for some multiplicative $\varphi$ (`hHsurj`); $\mathrm{pt}$ is injective on multiplicative $\varphi$ (`hHinj`); multiplicativity is stable under affine base change (`hbc`). Let $n \in \mathbb{N}$ and let $\pi_X : X \to \operatorname{Spec} R$ with $q_0,\dots,q_{n-1} : X \to H$ over $\pi_H$ be an $n$-fold fibre power of $H$ over $\operatorname{Spec} R$ (`hX`: unique factorisation of $n$-tuples of morphisms to $H$ over a common base morphism). Let $F$ assign to each $s$ and each $n$-tuple $(\varphi_l)$ of morphisms over $s$ a morphism $F_s(\varphi)$ over $s$ (`hF`), natural under base change along ring maps (`hFnat`). Then there exists $\mathrm{op} : X \to H$ with $\mathrm{op} \circ \pi_H = \pi_X$ such that for every $S'$, every $s$, every $n$-tuple $(\varphi_l)$ of multiplicative morphisms over $s$, and every $z : \operatorname{Spec} S' \to X$ with $z \circ \pi_X = s$ and $z \circ q_l = \mathrm{pt}(\varphi_l)$ for all $l$, one has $z$ followed by $\mathrm{op}$ equal to $\mathrm{pt}(F_s(\varphi))$. No uniqueness of $\mathrm{op}$ is asserted.
--
--   This is the representability step that turns an operation on $n$-tuples of group-law homomorphisms $A \times_R \operatorname{Spec} S' \to A$, natural in the affine base, into an actual $R$-morphism $H^{\times n} \to H$ of the scheme representing such homomorphisms, with the expected effect on affine points. It is used in the construction of the table scheme, [`AlgebraicGeometry.exists_tableScheme_of_represents_homScheme`](thm.html#AlgebraicGeometry.exists_tableScheme_of_represents_homScheme), within the Hom-scheme infrastructure for Néron models and good reduction of Jacobians; the proof cites the affine-point Yoneda principle [`AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver`](thm.html#AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_fibrePower_homScheme_of_naturalOperation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.exists_hom_fibrePower_homScheme_of_naturalOperation
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (H : Scheme.{u}) (πH : H ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f s ⟶ A), φ ≫ f = pullback.snd f s ≫ s → SchemeHomOver s πH)
    (hHnat : (∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1))
    (hHsurj : (∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x))
    (hHinj : (∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ φ' : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hφ' : φ' ≫ f = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ' =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ'))
    (hbc : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s)
        (φ'' : pullback f s'' ⟶ A) (hφ'' : φ'' ≫ f = pullback.snd f s'' ≫ s''),
        φ'' = pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') f),
          pullback.lift (L.mul (t' ≫ s'') P Q).1 t' (L.mul (t' ≫ s'') P Q).2 ≫ φ'' =
            (L.mul (t' ≫ s'')
              ⟨pullback.lift P.1 t' P.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩).1))
    (n : ℕ) (X : Scheme.{u}) (πX : X ⟶ Spec (CommRingCat.of R)) (q : Fin n → (X ⟶ H)) (hq : ∀ l, q l ≫ πH = πX)
    (hX : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) (g : Fin n → (T ⟶ H)), (∀ l, g l ≫ πH = t) →
        ∃! G : T ⟶ X, G ≫ πX = t ∧ ∀ l, G ≫ q l = g l)
    (F : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : Fin n → (pullback f s ⟶ A)), (∀ l, φ l ≫ f = pullback.snd f s ≫ s) → (pullback f s ⟶ A))
    (hF : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
        F S' s φ hφ ≫ f = pullback.snd f s ≫ s)
    (hFnat : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
        F S'' s'' (fun l => pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ l)
            (fun l => by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]) =
          pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ F S' s φ hφ) :
    ∃ op : X ⟶ H, op ≫ πH = πX ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
        (∀ l, (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ l =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd]⟩).1)) →
        ∀ z : SchemeHomOver s πX, (∀ l, z.1 ≫ q l = (pt S' s (φ l) (hφ l)).1) →
          z.1 ≫ op = (pt S' s (F S' s φ hφ) (hF S' s φ hφ)).1 := by sorry
