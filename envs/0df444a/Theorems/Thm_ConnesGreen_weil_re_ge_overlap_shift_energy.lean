-- Prove2me | Theorems.Thm_ConnesGreen_weil_re_ge_overlap_shift_energy
-- name    : ConnesGreen.weil_re_ge_overlap_shift_energy
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:44:22.813787+00:00
-- url     : https://prove2.me/theorems/d14c35c8-1fdf-44e1-a7f1-564be792a4e0
-- title:
--   Weil form bounded below by the improved physical-energy shift
-- statement:
--   For $R\ge0$ and an ORIGINAL smooth complex test $g$ supported in $[-R,R]$, let $E(g)=\int|g\prime|^2+\frac14\int|g|^2$ and let $K_R$ be the explicit arithmetic overlap shift. Then $$\Re W(g*g^*)\ge -K_R E(g).$$ This is an unconditional lower bound in the unchanged physical test energy. The native development also proves $0\le K_R\le K_R^{\mathrm{old}}$; the bound is not an assertion of unshifted Weil positivity or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/OverlapShiftCertificates.lean, exact declaration ConnesGreen.weil_re_ge_overlap_shift_energy, compiling local source d80c1a8e4c7f0442e092ecaaf726d7aa26822229. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.weil_re_ge_overlap_shift_energy (R : ℝ) (hR : 0 ≤ R)
    (g : ℝ → ℂ) (hg : SupportedTest R g) :
    -arithmeticOverlapShift R * physicalTestEnergy g ≤
      (weilDistribution (conv g (starInv g))).re := by sorry
