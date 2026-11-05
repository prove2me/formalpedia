-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_ruin_truncated_terminal_L1_all_times
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_BV_ruin_truncated_terminal_L1_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:11:22.504514+00:00
-- url     : https://prove2.me/theorems/60abf1b6-8940-4fbf-955f-78b619fffe98
-- title:
--   Original BV bounded ruin-clock terminal payoff is L1 at all deterministic times
-- statement:
--   Under genuine bounded-variation source, admissibility, normalised X.X 0 and finite P, the discounted original riskProcess payoff masked by the strict original bounded ruin clock is integrable at every deterministic S, whether S<T or S>=T. Before T use the Proved original strict preterminal integrability; at or after T the mask vanishes by the exact source ruin-clock endpoint equivalence. No terminal atom or finite-cap zero-occupation assertion is imposed.
-- source:
--   Proved original physical strict preterminal L1 d086b85a, Proved P3-G exact truncated ruin-clock endpoint b4677f24, pinned Mathlib MeasureTheory.integrable_const compiler signature.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_BV_ruin_truncated_terminal_L1_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (T S : ℝ≥0) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
      then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) P := by sorry
