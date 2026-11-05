-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_cdf_determines_separated_borel
-- name    : AvramDividend.Classical.avram_p2_a_assist_negative_cdf_determines_separated_borel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:24:48.661288+00:00
-- url     : https://prove2.me/theorems/1c22d817-e090-4dcb-b6ec-1eab567f1a5f
-- title:
--   Finite negative halfline CDF determines all separated negative Borel masses
-- statement:
--   For arbitrary locally finite-on-separated-negative-bands measures on the real line, equality of every negative halfline cutoff mass implies equality on any measurable subset of a negative separated band. Restrict to one finite band and apply the exact pinned Measure.ext_of_Iic uniqueness theorem, including boundary atoms.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_assist_negative_cdf_determines_separated_borel
    (μ ν : Measure ℝ)
    (hμBand : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hCuts : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) = ν (Iic (-δ)))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    μ B = ν B := by sorry
