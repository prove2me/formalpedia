-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
-- name    : AlgebraicGeometry.Scheme.exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b9fca7e3-536a-56d5-bf01-25a3e7aaba4d
-- title:
--   Open subfunctors with affine charts cover a Zariski sheaf
-- statement:
--   Let $R$ be a commutative ring and let $F$ assign a type $F(A)$ to every commutative $R$-algebra $A$, together with maps $\mathrm{Fmap}$ sending an $R$-algebra homomorphism $\varphi : A \to B$ to a map $F(A) \to F(B)$, assumed to respect identities and composition. Let $G$ be a presheaf of types on the category of schemes over $\operatorname{Spec} R$, so that `G.overTotal` is the presheaf on schemes sending $T$ to the type of pairs $(t, \xi)$ with $t : T \to \operatorname{Spec} R$ and $\xi \in G(T,t)$, and assume given bijections $\mathrm{ev}_A : F(A) \simeq G(\operatorname{Spec} A \to \operatorname{Spec} R)$ for all $A$, that `G.overTotal` is a sheaf for the Zariski topology on schemes, and that the $\mathrm{ev}_A$ are natural: for $\varphi : A \to_{R} B$, $s \in F(A)$ and any witness that $\operatorname{Spec}\varphi$ followed by $\operatorname{Spec}(\text{structure map of } A)$ is the structure map of $B$, $\mathrm{ev}_B(\mathrm{Fmap}\,\varphi\,s)$ is the image of $\mathrm{ev}_A(s)$ under $G$ applied to the resulting morphism over $\operatorname{Spec} R$. Let $\iota$ be an index type and $P_i$ a property of elements of $F(A)$ for each $i$ and each $A$, such that for every $i$, $A$ and $s \in F(A)$ there is an open $U \subseteq \operatorname{Spec} A$ with $P_i(\mathrm{Fmap}\,\varphi\,s)$ holding precisely when the range of $\operatorname{Spec}\varphi$ lies in $U$, for all $\varphi : A \to_R B$. Let $S_i$ be commutative $R$-algebras with bijections $\{s \in F(A) : P_i(s)\} \simeq \operatorname{Hom}_{R\text{-alg}}(S_i, A)$, natural in $A$ in the sense that the chart of $\mathrm{Fmap}\,\varphi\,s$ is $\varphi$ composed with the chart of $s$; and assume that for every field $K$ over $R$ every element of $F(K)$ satisfies some $P_i$. Then there are morphisms of presheaves $f_i$ from the functor of points of $\operatorname{Spec} S_i$ to `G.overTotal` such that each $f_i$ satisfies `IsOpenImmersion.presheaf`, the morphism induced by the $f_i$ out of the coproduct is locally surjective for the Zariski topology, and $f_i$ sends the identity of $\operatorname{Spec} S_i$ to the pair consisting of the structure morphism $\operatorname{Spec} S_i \to \operatorname{Spec} R$ and $\mathrm{ev}_{S_i}$ of the element of $F(S_i)$ whose chart is the identity of $S_i$.
--
--   This is the input step for checking representability of a moduli functor locally: a functor on commutative $R$-algebras presented by open subfunctors with affine charts, whose associated total presheaf on schemes is a Zariski sheaf, admits a family of relatively representable open immersions from affine schemes that is jointly locally surjective. It is used by [`AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover`](thm.html#AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover), where the local criterion for representability is then applied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.lean

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    (Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s))
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type)
    (ev : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))))
    (hG : Presheaf.IsSheaf Scheme.zariskiTopology G.overTotal)
    (hev : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
      (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      ev B (Fmap A B φ s) =
        G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s))
    (ι : Type) (P : ι → ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (isOpen : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : F A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
          P i B (Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U)
    (S : ι → Type) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (chart : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A], {s : F A // P i A s} ≃ (S i →ₐ[R] A))
    (chart_natural : ∀ (i : ι) (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : {s : F A // P i A s}) (h : P i B (Fmap A B φ s.1)),
      chart i B ⟨Fmap A B φ s.1, h⟩ = φ.comp (chart i A s))
    (cover : ∀ (K : Type) [Field K] [Algebra R K] (s : F K), ∃ i, P i K s) :
    ∃ f : ∀ i, yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ G.overTotal,
      (∀ i, IsOpenImmersion.presheaf (f i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) ∧
      ∀ i, (f i).app (op (Spec (CommRingCat.of (S i)))) (𝟙 (Spec (CommRingCat.of (S i)))) =
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R (S i))),
          ev (S i) ((chart i (S i)).symm (AlgHom.id R (S i))).1⟩ := by sorry
