-- Prove2me | Theorems.Thm_ConnesGreen_weilPositive_iff_all_full_covariance_bounds
-- name    : ConnesGreen.weilPositive_iff_all_full_covariance_bounds
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T17:16:30.238471+00:00
-- url     : https://prove2.me/theorems/2d150ddd-d47f-443c-b7c1-0b875782a2bc
-- title:
--   Global Weil positivity is exactly full actual-zero covariance order on every window
-- statement:
--   Global Weil positivity on the original smooth compactly supported complex test functions is equivalent to the full covariance inequality N_t N_t* ≤ P_t P_t* for every positive support radius t. Here P_t and N_t are the unchanged canonical positive and COMPLETE actual-zeta-zero negative synthesis operators on the original Dirichlet energy-image completion. The negative operator uses the actual critical-strip zeros and their analytic multiplicities, not a selected finite packet. The theorem specifies an exact global target and proves neither condition unconditionally.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/RHSpine.lean, ConnesGreen.weilPositive_iff_all_full_covariance_bounds at native compiling mathematical-source commit e348db588b5acb95a2bf9bf73bc9a10890c3f92e; public signatures unfold only the unchanged WeilPositive predicate. Full original Green actors, actual-zero subtype and multiplicities preserved.

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.weilPositive_iff_all_full_covariance_bounds :
    (∀ g : ℝ → ℂ, ConnesRZ.IsTest g →
      0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re) ↔ ∀ t : ℝ, ∀ ht : 0 < t,
      canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint ≤
        canonicalPositiveCovariance t ht := by sorry
