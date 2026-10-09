-- Prove2me | Theorems.Thm_ConnesGreen_weil_convolution_re_ge_frequency_mass_energy_budget
-- name    : ConnesGreen.weil_convolution_re_ge_frequency_mass_energy_budget
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T00:41:06.167141+00:00
-- url     : https://prove2.me/theorems/fe5c96b7-919b-467b-bd78-0f8dbeb3c172
-- title:
--   Weil arithmetic lower bound with the smaller mass or energy prime loss
-- statement:
--   For $B,T\ge0$ and an original smooth test $g$ supported in $[-T,T]$, put $h=g*g^*$, $M=\int|g|^2$, $E=\int|g\prime|^2+M/4$, and $P_T=\sum_{n\in A_T}\Lambda(n)/\sqrt n$. With $\gamma(r)=\Re\psi(1/4+ir/2)-\log\pi$, the original Weil distribution satisfies $$\Re W(h)\ge [\gamma(B)-(\gamma(B)-\gamma(0))2BT/\pi-4Te^T]M-\min(2P_TM,8TP_TE).$$ This combines the existing archimedean and pole estimates with both complete prime estimates. No nonnegativity of the displayed lower bound is claimed; it is an unconditional quantitative bound, not an RH proof or a cofinal-window certificate.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ArithmeticMassBudget.lean, declaration ConnesGreen.weil_convolution_re_ge_frequency_mass_energy_budget, compiling local source 8374c1d6419c567e9c1319e441c6a1348d0d0969. Original definitions and test class retained.

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative

theorem ConnesGreen.weil_convolution_re_ge_frequency_mass_energy_budget
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (Zeta23.EF.gammaBracket B -
      (Zeta23.EF.gammaBracket B - Zeta23.EF.gammaBracket 0) *
        (2 * B * T / Real.pi) - 4 * T * Real.exp T) * (∫ s : ℝ, ‖g s‖ ^ 2) -
      min (2 * activePrimeWeight T * (∫ s : ℝ, ‖g s‖ ^ 2))
        (8 * T * activePrimeWeight T * physicalTestEnergy g) ≤
          (weilDistribution (conv g (starInv g))).re := by sorry
