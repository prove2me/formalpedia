-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
-- name    : AlgebraicGeometry.Scheme.exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b2336c5b-96bc-541e-937c-57d2fdb30460
-- title:
--   Overlaps of away-localisation charts are again away charts
-- statement:
--   Fix a commutative ring $S$, a natural number $k$, elements $r : \mathrm{Fin}\,k \to S$, and commutative rings $B_i$ ($i \in \mathrm{Fin}\,k$) which are $S$-algebras exhibiting $B_i$ as a localisation of $S$ away from $r_i$. Let $f : Y \to \operatorname{Spec} S$ be a morphism of schemes, and for each $i$ let $f'_i : A'_i \to \operatorname{Spec} B_i$ be a morphism and $\iota_i : A'_i \to Y$ an open immersion, such that for every $i$ the square with horizontal arrows $\iota_i$ and $\operatorname{Spec}$ of the structure map $S \to B_i$, and vertical arrows $f'_i$ and $f$, is cartesian. Then for every pair of indices $i, j$ there exist an $S$-algebra homomorphism $\rho_1 : B_i \to \mathrm{Localization.Away}\,(r_i r_j)$ and a morphism $f_P$ from the fibre product $A'_i \times_Y A'_j$ to $\operatorname{Spec}\bigl(\mathrm{Localization.Away}\,(r_i r_j)\bigr)$ such that: regarding $\mathrm{Localization.Away}\,(r_i r_j)$ as a $B_i$-algebra via $\rho_1$, it is a localisation of $B_i$ away from the image of $r_j$ in $B_i$; the square with horizontal arrows the first projection $A'_i \times_Y A'_j \to A'_i$ and $\operatorname{Spec} \rho_1$, and vertical arrows $f_P$ and $f'_i$, is cartesian; and $f_P$ followed by $\operatorname{Spec}$ of the $S$-algebra structure map $S \to \mathrm{Localization.Away}\,(r_i r_j)$ equals the first projection followed by $\iota_i$ followed by $f$.
--
--   This is the compatibility statement needed to descend data given chart by chart on a scheme over $\operatorname{Spec} S$ covered by open pieces which are base changes along the away-localisations $S \to S[1/r_i]$: the pairwise overlap $A'_i \times_Y A'_j$ is itself an affine-base chart, over $\operatorname{Spec} S[1/r_i r_j]$, compatibly with the $i$-th chart. It is used in the constructions of triple overlaps and of sections over overlaps in the same chart formalism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (i j : Fin k) :
    ∃ (ρ₁ : B i →ₐ[S] Localization.Away (r i * r j))
      (fP : Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j)))),
      (letI := ρ₁.toRingHom.toAlgebra
       IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j))) ∧
      CategoryTheory.IsPullback (Limits.pullback.fst (ι i) (ι j)) fP (f' i) (Spec.map (CommRingCat.ofHom ρ₁.toRingHom)) ∧
      fP ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) =
        Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f := by sorry
