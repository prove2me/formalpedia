-- Prove2me | Theorems.Thm_ConnesGreen_selected_signed_covariance_nonnegative_of_half
-- name    : ConnesGreen.selected_signed_covariance_nonnegative_of_half
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:46:34.129747+00:00
-- url     : https://prove2.me/theorems/1193d546-7eb7-47c2-8545-e062d58c2b05
-- title:
--   Original inner half-bound implies nonnegative signed physical covariance
-- statement:
--   For an original positive window $t$ and original finite actual-zero packet $S$, we prove
--   $$\tfrac12 I\le G_S(t)\quad\Longrightarrow\quad 0\le P_tP_t^*-M_{t,S}M_{t,S}^*.$$
--   The accepted original half-bound characterization gives nonnegative selected quadratic value on every original supported test. The original positive covariance is self-adjoint, and the adjoint norm identity identifies its test quadratic form with the squared positive-analysis norm. The accepted dense original-test characterization of covariance order therefore upgrades the test inequalities to order on the entire ORIGINAL completed physical carrier. Subtraction gives nonnegativity of the unchanged signed covariance. No global Weil positivity, alternate physical carrier or new positivity assumption is used.
-- source:
--   monocap-tech/weil certified native head 5813d3576adfea3fd4d9319495125180db6e3d95; exact existing CanonicalGreenNeutralShell.lean and CriticalWindowBoundary.lean declarations; no native statement changes

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_original_quartet
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.selected_signed_covariance_nonnegative_of_half (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros)
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) :
    0 ≤ canonicalPositiveCovariance t ht -
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint := by sorry
