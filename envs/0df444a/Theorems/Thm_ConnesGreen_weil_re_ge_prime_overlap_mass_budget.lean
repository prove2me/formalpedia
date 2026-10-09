-- Prove2me | Theorems.Thm_ConnesGreen_weil_re_ge_prime_overlap_mass_budget
-- name    : ConnesGreen.weil_re_ge_prime_overlap_mass_budget
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:01:07.843568+00:00
-- url     : https://prove2.me/theorems/d6c3afe5-8eee-4aaf-b2cd-a13be2718a3f
-- title:
--   Weil lower bound with individual prime overlaps and signed pole loss
-- statement:
--   For $B,T\ge0$ and an original smooth compact complex test $g$ supported in $[-T,T]$, let $h=g*g^*$, $M(g)=\int|g|^2$, $\gamma(r)=\Re\psi(1/4+ir/2)-\log\pi$, and let $L_T(g)$ be the complete termwise prime mass/overlap loss. Then the original Weil form satisfies $$\Re W(h)\ge[\gamma(B)-(\gamma(B)-\gamma(0))2BT/\pi-2(\sinh T-T)]M(g)-L_T(g).$$ The native development also proves $L_T(g)\le\min(2P_TM(g),8TP_TE(g))$, so this bound is at least as strong as the preceding global-minimum prime budget. The displayed lower bound is not asserted nonnegative; the cofinal selected-correction sign obligation and RH remain open.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PrimeOverlapMass.lean, exact declaration ConnesGreen.weil_re_ge_prime_overlap_mass_budget, compiling local source 495a9f34f25d1dbfbeb6ba8dce6d4735559ae878. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_prime_overlap_loss
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen

theorem ConnesGreen.weil_re_ge_prime_overlap_mass_budget
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (Zeta23.EF.gammaBracket B -
      (Zeta23.EF.gammaBracket B - Zeta23.EF.gammaBracket 0) *
        (2 * B * T / Real.pi) - 2 * (Real.sinh T - T)) * (∫ s : ℝ, ‖g s‖ ^ 2) -
      primeOverlapLoss T g ≤ (weilDistribution (conv g (starInv g))).re := by sorry
