-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_cross_window_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_chronological_cross_window_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:53:36.806229+00:00
-- url     : https://prove2.me/theorems/a8adacce-d329-4357-b1cc-4e89615caf5b
-- title:
--   Same-original-process chronological cross-window negative-band jump count has its exact source mean product
-- statement:
--   For any original spectrally negative Lévy path X and deterministic 0≤s≤t, the product of actual marked count Jpast on (0,s]×(-∞,-1/(n+1)] and actual future count Jfuture on (s,t] in the identical mark band has ENNReal expectation E[Jpast]*(t-s)ν(B). No past-count measurability, frozen-path regularity, moment, independence, or replacement Poisson hypothesis is added: the proved original raw-filtration adaptation supplies the past weight and proved original P2-E supplies the genuine future mean factor. This is the exact ordered-cell cross term needed for finite-grid approximation to chronological pair expectation.
-- source:
--   The exact unproved source pair mean d938e9a5 is reduced via dyadic original marked count cross terms. Uses Proved P2-E 12ff9a1a and original deterministic-time past adaptation 41007669 after its accepted status; requires separate pathwise chronological grid refinement/monotone convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_chronological_cross_window_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    let Jpast : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    (∫⁻ ω, Jpast ω * Jfuture ω ∂P) =
      (∫⁻ ω, Jpast ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) *
          X.ν (Iic (-(1 / ((n : ℝ) + 1))))) := by sorry
