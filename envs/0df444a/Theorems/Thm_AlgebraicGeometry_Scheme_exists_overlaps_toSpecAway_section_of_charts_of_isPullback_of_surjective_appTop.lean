-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
-- name    : AlgebraicGeometry.Scheme.exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1d930793-74cd-50e3-bb6b-6f179cfdf743
-- title:
--   Overlap charts and sections for a localisation-away cover
-- statement:
--   Fix a commutative ring $S$, a natural number $k$, elements $r : \mathrm{Fin}\,k \to S$ and commutative $S$-algebras $B i$ each of which is a localisation of $S$ away from $r i$. Given a scheme morphism $f : Y \to \operatorname{Spec} S$, schemes $A' i$ with morphisms $f' i : A' i \to \operatorname{Spec}(B i)$ and open immersions $\iota i : A' i \to Y$, assume: (`hsq`) each square with $\iota i$, $f' i$, $f$ and $\operatorname{Spec}$ of $S \to B i$ is cartesian; (`hΓ`) for each $i$ the ring map on global sections induced by $f' i$ is surjective, and likewise for the second projection of the base change of $f' i$ along $\operatorname{Spec}$ of $B i \to (B i)[1/t]$, for every $t \in B i$; (`he`) sections $e i$ of $f' i$ are given, $e i \circ f' i$ being the identity in diagrammatic order; and (`heagree`) for all $i,j$, every $S$-algebra $C$ that is a localisation of $S$ away from $r i r_j$ and all $S$-algebra maps $\rho_1 : B i \to C$, $\rho_2 : B j \to C$, the two composites $\operatorname{Spec}(\rho_1)$ followed by $e i$ followed by $\iota i$ and $\operatorname{Spec}(\rho_2)$ followed by $e j$ followed by $\iota j$ into $Y$ coincide. The conclusion asserts the existence of $S$-algebra maps $\rho_1^{ij} : B i \to C_{ij}$ and $\rho_2^{ij} : B j \to C_{ij}$, where $C_{ij} =$ `Localization.Away (r i * r j)`, together with morphisms $f_{ij} : A' i \times_Y A' j \to \operatorname{Spec} C_{ij}$ and $e_{ij}$ in the other direction, such that: $e_{ij}$ followed by $f_{ij}$ is the identity; $f_{ij}$ followed by $\operatorname{Spec}$ of $S \to C_{ij}$ equals the first projection followed by $\iota i$ followed by $f$; $e_{ij}$ followed by the first (resp. second) projection equals $\operatorname{Spec}(\rho_1^{ij})$ followed by $e i$ (resp. $\operatorname{Spec}(\rho_2^{ij})$ followed by $e j$); the global-sections map of $f_{ij}$ is surjective, as is that of the second projection of the base change of $f_{ij}$ along $\operatorname{Spec}$ of $C_{ij} \to C_{ij}[1/r']$ for every $r' \in C_{ij}$; and finally, for all triples $i,j,l$ and every morphism $\pi_{13}$ from $T = (A' i \times_Y A' j) \times_{A' j} (A' j \times_Y A' l)$ to $A' i \times_Y A' l$ compatible with the outer projections as specified by $h_1$ and $h_3$, there exist a morphism $f_T : T \to \operatorname{Spec} C_{ijl}$ with $C_{ijl} =$ `Localization.Away (r i * r j * r l)`, a section $e_T$ of it with surjective global-sections map for $f_T$, and $S$-algebra maps $\sigma_{12} : C_{ij} \to C_{ijl}$, $\sigma_{23} : C_{jl} \to C_{ijl}$, $\sigma_{13} : C_{il} \to C_{ijl}$ such that $e_T$ followed by each of the two projections of $T$, and $e_T$ followed by $\pi_{13}$, equal $\operatorname{Spec}(\sigma_{12})$ followed by $e_{ij}$, $\operatorname{Spec}(\sigma_{23})$ followed by $e_{jl}$, and $\operatorname{Spec}(\sigma_{13})$ followed by $e_{il}$ respectively.
--
--   This packages the descent bookkeeping for a cover of $\operatorname{Spec} S$ by the principal opens $D(r_i)$: from charts $A' i$ of $Y$ over $\operatorname{Spec}(B i)$ with rigidifying sections $e i$ it produces, on every pairwise overlap $A' i \times_Y A' j$ and every triple overlap, a structure morphism to the spectrum of the corresponding multiple localisation, a compatible section, and the surjectivity of global sections needed to repeat the construction after a further localisation. It is used in the construction of pullback isomorphisms satisfying the cocycle condition for invertible modules over such charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hΓ : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r : B i, Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (B i) (Localization.Away r))))).appTop).hom)
    (e : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A' i) (he : ∀ i, e i ≫ f' i = 𝟙 _)
    (heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
        (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e i ≫ ι i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e j ≫ ι j) :
    ∃ (ρ₁ : ∀ i j : Fin k, B i →ₐ[S] Localization.Away (r i * r j))
      (ρ₂ : ∀ i j : Fin k, B j →ₐ[S] Localization.Away (r i * r j))
      (fP : ∀ i j : Fin k,
        Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))))
      (eP : ∀ i j : Fin k,
        Spec (CommRingCat.of (Localization.Away (r i * r j))) ⟶ Limits.pullback (ι i) (ι j)),

      (∀ i j, eP i j ≫ fP i j = 𝟙 _) ∧
      (∀ i j, fP i j ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) =
        Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ∧
      (∀ i j, eP i j ≫ Limits.pullback.fst (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom) ≫ e i) ∧
      (∀ i j, eP i j ≫ Limits.pullback.snd (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom) ≫ e j) ∧
      (∀ i j, Function.Surjective ((fP i j).appTop).hom) ∧
      (∀ (i j : Fin k) (r' : Localization.Away (r i * r j)), Function.Surjective
        ((pullback.snd (fP i j) (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away (r i * r j)) (Localization.Away r'))))).appTop).hom) ∧

      (∀ (i j l : Fin k)
        (π₁₃ : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶
          Limits.pullback (ι i) (ι l))
        (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) =
          (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫
            Limits.pullback.fst (ι i) (ι j))
        (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) =
          (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫
            Limits.pullback.snd (ι j) (ι l)),
        ∃ (fT : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶
              Spec (CommRingCat.of (Localization.Away (r i * r j * r l))))
          (eT : Spec (CommRingCat.of (Localization.Away (r i * r j * r l))) ⟶
              Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))
          (σ₁₂ : Localization.Away (r i * r j) →ₐ[S] Localization.Away (r i * r j * r l))
          (σ₂₃ : Localization.Away (r j * r l) →ₐ[S] Localization.Away (r i * r j * r l))
          (σ₁₃ : Localization.Away (r i * r l) →ₐ[S] Localization.Away (r i * r j * r l)),
          eT ≫ fT = 𝟙 _ ∧ Function.Surjective (fT.appTop).hom ∧
          eT ≫ Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) =
            Spec.map (CommRingCat.ofHom σ₁₂.toRingHom) ≫ eP i j ∧
          eT ≫ Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) =
            Spec.map (CommRingCat.ofHom σ₂₃.toRingHom) ≫ eP j l ∧
          eT ≫ π₁₃ = Spec.map (CommRingCat.ofHom σ₁₃.toRingHom) ≫ eP i l) := by sorry
