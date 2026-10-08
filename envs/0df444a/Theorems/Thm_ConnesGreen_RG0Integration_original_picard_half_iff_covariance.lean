-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_original_picard_half_iff_covariance
-- name    : ConnesGreen.RG0Integration.original_picard_half_iff_covariance
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:04:57.733821+00:00
-- url     : https://prove2.me/theorems/f4c987a5-49ea-425b-bfd6-30b1dcf4bd14
-- title:
--   Original inner half-bound is exactly physical covariance domination
-- statement:
--   Fix a positive original window $t$ and an unchanged finite actual-zero packet $S$. Let $C_t$ be its constructed Picard marker, $N_t$ its original selected synthesis, and $A_t$ its full original positive covariance. Then $$\tfrac12 I\le C_t\quad\Longleftrightarrow\quad N_tN_t^*\le A_t.$$ First use the accepted original all-positive-regularizations equivalence. For every $\varepsilon>0$, the accepted Schur half-bound theorem applies to $A_t+\varepsilon I$, which is strictly positive. Operator order is closed under the limit $\varepsilon\downarrow0$, giving the unregularized covariance inequality. The reverse direction uses $A_t\le A_t+\varepsilon I$. The original physical carrier and actual-zero actors are unchanged; $A_t$ itself may be singular, and no inverse of $A_t$ is used. Neither inequality is asserted true.
-- source:
--   monocap-tech/weil; original CanonicalGreenFiniteOffline.lean and RG0QuartetCutEndpoint.lean. Original carrier, covariance, selected packet and constructed Picard marker preserved.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.MarkerStability
open scoped InnerProductSpace lp Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section

theorem ConnesGreen.RG0Integration.original_picard_half_iff_covariance
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint ≤
      canonicalPositiveCovariance t ht := by sorry
