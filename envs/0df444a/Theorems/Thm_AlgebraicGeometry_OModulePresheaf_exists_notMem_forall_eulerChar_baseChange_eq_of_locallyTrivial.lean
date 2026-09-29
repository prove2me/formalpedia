-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/a9ae03fd-05ac-549b-a40f-198f2fb84533
-- title:
--   Local constancy of fibrewise Euler characteristic on a basic open
-- statement:
--   Let $S$ be a noetherian commutative ring, let $X$ be a scheme and let $\pi : X \to \operatorname{Spec} S$ be proper and flat, and let $M$ be a sheaf of modules on $X$. Assume $M$ is locally trivial in the sense that every point $x \in X$ lies in an open $U$ for which the pull-back of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules, to the unit sheaf of modules on $U$. Let $\mathcal{U}$ be an ordered affine cover of $X$, that is, a finite linearly ordered family of affine opens whose supremum is $\top$, and let $\mathfrak{p}$ be a prime of $S$. Then there exist $g \in S$ with $g \notin \mathfrak{p}$ and an integer $\chi_0$ such that for every field $k$ (in the same universe) equipped with an $S$-algebra structure sending $g$ to a non-zero element, the following holds: form the pull-back $X \times_{\operatorname{Spec} S} \operatorname{Spec} k$, pull $M$ back along the first projection, and regard its sections as a presheaf of $k$-modules via the second projection to $\operatorname{Spec} k$; then the Euler characteristic $\sum_i (-1)^i \dim_k \check{H}^i$ of this presheaf computed with the base-changed cover $\mathcal{U}$ (the preimages of the $\mathcal{U}_i$ under the first projection) equals $\chi_0$.
--
--   This is the local constancy on the base of the Euler characteristic of the fibres of a proper flat family, for a module locally isomorphic to the structure sheaf, in the form of constancy of the Čech Euler characteristic across all field-valued points of a basic open neighbourhood of a given prime. It is used in the study of the Jacobian of a curve with good reduction, to produce a basic open on which the dimension of the sections over geometric fibres is positive.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
    {S : Type u} [CommRing S] [IsNoetherianRing S] {X : Scheme.{u}} (π : X ⟶ Spec (.of S))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (𝔭 : PrimeSpectrum S) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∃ χ₀ : ℤ, ∀ (k : Type u) [Field k] [Algebra S k], algebraMap S k g ≠ 0 →
      (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap S k))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap S k))).obj M)).eulerChar (𝒰.baseChange π k)
        = χ₀ := by sorry
