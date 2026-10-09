-- Prove2me | Theorems.Thm_ConnesGreen_pole_pair_re_ge_sinh_mass
-- name    : ConnesGreen.pole_pair_re_ge_sinh_mass
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T02:43:44.865074+00:00
-- url     : https://prove2.me/theorems/b8e34337-05e0-45cb-b750-8eb7eb0be814
-- title:
--   Signed pole loss controlled by the exact odd support weight
-- statement:
--   Let $T\ge0$ and let $g:\mathbb R\to\mathbb C$ be an original smooth compact test supported in $[-T,T]$. Write $h=g*g^*$, $g^*(t)=\overline{g(-t)}$, and $M=\int_{\mathbb R}|g(t)|^2\,dt$. The original Mellin pole pair satisfies $$\Re[\widehat h(0)+\widehat h(1)]\ge -2(\sinh T-T)M.$$ Only the negative odd square is charged. The positive even square is retained, and the original transforms and admissible-test class are unchanged. The native development also proves $2(\sinh T-T)<4Te^T$ for every $T>0$, a strict improvement over the preceding absolute pole loss. This is a signed pole estimate, not a positivity or RH assertion.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/SignedPoleMass.lean, exact declaration ConnesGreen.pole_pair_re_ge_sinh_mass, compiling local source ccfcc3063030f0cce8dc2c71697d762fe2da201f. Original canonical model, Mellin normalization and arithmetic definitions retained.

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen

theorem ConnesGreen.pole_pair_re_ge_sinh_mass (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    -2 * (Real.sinh T - T) * (∫ s : ℝ, ‖g s‖ ^ 2) ≤
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re := by sorry
