-- Prove2me | Theorems.Thm_ConnesGreen_weil_re_ge_signed_pole_mass_energy_budget
-- name    : ConnesGreen.weil_re_ge_signed_pole_mass_energy_budget
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T02:47:02.22677+00:00
-- url     : https://prove2.me/theorems/3f450682-445b-4d96-b8dc-682c86dfdb17
-- title:
--   Weil lower bound retaining the positive pole square
-- statement:
--   Let $B,T\ge0$ and let $g$ be an original smooth test supported in $[-T,T]$. Put $h=g*g^*$, $M=\int|g|^2$, $E=\int|g\prime|^2+M/4$, $P_T=\sum_{n\in A_T}\Lambda(n)/\sqrt n$, and $\gamma(r)=\Re\psi(1/4+ir/2)-\log\pi$, where $A_T$ contains exactly the prime powers with $\log n<2T$. Then $$\Re W(h)\ge[\gamma(B)-(\gamma(B)-\gamma(0))2BT/\pi-2(\sinh T-T)]M-\min(2P_TM,8TP_TE).$$ The complete original prime contribution is paid using the smaller of the accepted mass and energy bounds, and the pole loss uses the signed odd-square estimate. No nonnegativity of this quantitative budget is asserted. The cofinal selected-correction sign obligation and RH remain open.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/SignedPoleMass.lean, exact declaration ConnesGreen.weil_re_ge_signed_pole_mass_energy_budget, compiling local source ccfcc3063030f0cce8dc2c71697d762fe2da201f. Original canonical model, Mellin normalization and arithmetic definitions retained.

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen

theorem ConnesGreen.weil_re_ge_signed_pole_mass_energy_budget
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (Zeta23.EF.gammaBracket B -
      (Zeta23.EF.gammaBracket B - Zeta23.EF.gammaBracket 0) *
        (2 * B * T / Real.pi) - 2 * (Real.sinh T - T)) * (∫ s : ℝ, ‖g s‖ ^ 2) -
      min (2 * activePrimeWeight T * (∫ s : ℝ, ‖g s‖ ^ 2))
        (8 * T * activePrimeWeight T * physicalTestEnergy g) ≤
          (weilDistribution (conv g (starInv g))).re := by sorry
