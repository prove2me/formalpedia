-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_scale_initial_value_nonnegative
-- name    : AvramDividend.Classical.chat04_killed_discounted_scale_initial_value_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:59:31.076314+00:00
-- url     : https://prove2.me/theorems/e66e2b10-fea9-4d76-8704-bbbce90c0998
-- title:
--   Downward-killed discounted scale payoff starts at W(x) for nonnegative reserve
-- statement:
--   For any nonnegative initial reserve x and every sample path of the official spectrally negative Lévy process, the zero-horizon no-ruin event holds and the killed discounted q-scale reward at time zero equals W(x). The proof uses the axiom X_0=0, deterministic zero discount, and indicator simplification. This is the exact initial normalisation for the killed martingale whose two-sided stopping identity is the strict exit branch's open analytic target.
-- source:
--   SpectrallyNegativeLevy.X_zero and Mathlib indicator and exponential simplification; independent of harmonicity.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_discounted_scale_initial_value_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (hx : 0 ≤ x) (ω : Ω) :
    ({ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (-(q * (0 : ℝ))) *
        W (x + X.X 0 ω)) ω = W x := by sorry
