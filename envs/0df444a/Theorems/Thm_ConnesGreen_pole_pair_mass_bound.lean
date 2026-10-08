-- Prove2me | Theorems.Thm_ConnesGreen_pole_pair_mass_bound
-- name    : ConnesGreen.pole_pair_mass_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:44:41.796995+00:00
-- url     : https://prove2.me/theorems/3b3e7b6c-5884-4b63-87f4-c4dc02fd78c0
-- title:
--   Original mixed pole pair is controlled by support length and original test mass
-- statement:
--   For $T\ge0$ and an unchanged original admissible test $g$ supported in $(-T,T)$, $$\left|\widehat{g*g^*}(0)+\widehat{g*g^*}(1)\right|\le4T e^T\int_{\mathbb R}|g(s)|^2\,ds.$$ The accepted original support-mass Mellin bound controls both pole transforms, and the accepted original convolution/involution identity gives their mixed conjugate products. Triangle and arithmetic-geometric mean inequalities prove the bound. The mass is an auxiliary arithmetic quantity, not a replacement physical metric. No gamma, zero-tail, positivity or RH premise is used.
-- source:
--   monocap-tech/weil at b0fd3ea4942154e083984fda035eff95e0a8de48; exact native signatures from SmallSupportPositivity.lean. Accepted original Mellin and overlap interfaces are reused. Native declarations are unchanged.

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

theorem ConnesGreen.pole_pair_mass_bound (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1‖ ≤
      4 * T * Real.exp T * (∫ s : ℝ, ‖g s‖ ^ 2) := by sorry
