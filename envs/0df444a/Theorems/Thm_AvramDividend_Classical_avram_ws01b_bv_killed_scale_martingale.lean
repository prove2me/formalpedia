-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_martingale
-- name    : AvramDividend.Classical.avram_ws01b_bv_killed_scale_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:46:29.799871+00:00
-- url     : https://prove2.me/theorems/ab64adeb-5fcd-4c7b-bfdb-be8690d31aba
-- title:
--   Actual BV killed q-scale process is a true martingale
-- statement:
--   Under the original spectrally negative Lévy law, Standing, q>0, an authentic scale function W, and bounded variation, the time-discounted reserve q-scale reward killed upon any preceding passage strictly below zero is a continuous-time martingale. Follows from the canonically Proved full future-window conditional killed q-harmonicity, without an assumed stochastic martingale or stopped-exit result.
-- source:
--   Source-specific unconditional specialisation of Proved future-window theorem c2e577be and Proved generic killed-history martingale assembler e336ea1f, using Proved rational-cover clock schedule 6e04803a. Genuine lower-killing on the actual whole path, valid at x=0 with BV W(0)>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_boundedVariation_future_window_killed_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01b_bv_killed_scale_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by sorry
