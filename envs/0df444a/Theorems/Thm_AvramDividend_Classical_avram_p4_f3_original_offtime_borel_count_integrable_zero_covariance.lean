-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
-- name    : AvramDividend.Classical.avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:54:39.241672+00:00
-- url     : https://prove2.me/theorems/c42c7851-620a-4af9-8353-abecd0320ce7
-- title:
--   Original physical off-time Borel count covariance has finite L1 norm and vanishes
-- statement:
--   The literal original past centred halfline jump count and a later centred marked Borel count have an integrable product and zero physical cross-moment. Separate original L2 bounds supply L1 by Holder; the original conditional-expectation orthogonality yields zero integral. It advances off-diagonal finite-grid martingale isometry without an independent copy.
-- source:
--   Derivation from Proved original past full-band L2 and future Borel L2 via MemLp.integrable_mul, plus original chronological conditional product-zero theorem 9c10168f (requires Proved/public) and pinned integral_condExp. Original P, original marked jump count, exact Mathlib 0df444a.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_past_full_band_future_borel_cross_condExp_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n m : ℕ)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((m : ℝ) + 1)))) :
    let Jpast : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let rp : ℝ :=
      ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((Jpast ω).toReal - rp) *
      ((Jfuture ω).toReal - rf)) P ∧
      ∫ ω, ((Jpast ω).toReal - rp) *
        ((Jfuture ω).toReal - rf) ∂P = 0 := by sorry
