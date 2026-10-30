-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_future_window_killed_scale_harmonicity
-- name    : AvramDividend.Classical.boundedVariation_future_window_killed_scale_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:41:33.834355+00:00
-- url     : https://prove2.me/theorems/c2e577be-5884-4f57-a335-7bf54c94da92
-- title:
--   Future-window killed q-scale harmonicity under bounded variation
-- statement:
--   For a spectrally negative Levy process under the standing assumptions with a q-scale function W and finite-variation paths, the conditional expectation given F_s of the discounted scale value at u over paths staying nonnegative on the window [s,u] equals the scale value at s, almost surely. This is the one-step future-window killed q-harmonicity of the scale function: the exact missing premise (hFuture) of the Proved killed-conditional-expectation theorem chat04_killed_condExp_of_future_window_harmonicity, which via the Proved time-split chat04_standing_killed_discounted_condExp_time_split bridges to the bounded-variation stopped-scale balance.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1: the killed q-scale martingale stated as (3.7) on pp. 7-8 of the PDF (as shown in [21, Prop. 3], Kyprianou-Palmowski fluctuation theory), here in one-window conditional form. Bounded-variation scoping matches the parent chain (bounded-variation stopped-scale balance 2bb529c8 within mission 1300fbe7); it isolates the E01 unsolved-goals residual of CE candidate 16067, whose Proved legs (pointwise payoff 3a6690c2, factorisation e1242e81, measurability 065fe2d0, positivity 59531c77) all elaborate. No Open exit theorem is cited, so the child is cycle-free.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem boundedVariation_future_window_killed_scale_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω)) := by
  sorry

end AvramDividend.Classical
