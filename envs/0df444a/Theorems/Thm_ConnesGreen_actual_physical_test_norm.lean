-- Prove2me | Theorems.Thm_ConnesGreen_actual_physical_test_norm
-- name    : ConnesGreen.actual_physical_test_norm
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T07:07:40.138956+00:00
-- url     : https://prove2.me/theorems/4fe90a41-6853-4bd5-bc89-4a1e6e3997bb
-- title:
--   Original physical source norm equals global Dirichlet test energy
-- statement:
--   For $t>0$ and an original smooth test $g$ supported inside $(-t,t)$, the original source representative of $Lg$ satisfies $\|\operatorname{sourceEmbed}_t(Lg)\|^2=\int_{\mathbb R}|g^\prime(x)|^2\,dx+\tfrac14\int_{\mathbb R}|g(x)|^2\,dx$. Thus its physical norm is independent of any enclosing support window. This is the certified original Green quotient carrier and original Dirichlet metric, with no new metric, carrier replacement or extra norm premise.
-- source:
--   monocap-tech/weil native base b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new sources Screening/MarkerMargin.lean and Connes/CanonicalGreenMarkerMargin.lean in Connes_Weil_Uniform_Marker_Margin.zip. Explicit reductions, not unconditional arithmetic marker positivity or RH.

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped InnerProductSpace

theorem ConnesGreen.actual_physical_test_norm (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖sourceEmbed t (problemOneL g)‖ ^ 2 =
      (∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
      (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2) := by sorry
