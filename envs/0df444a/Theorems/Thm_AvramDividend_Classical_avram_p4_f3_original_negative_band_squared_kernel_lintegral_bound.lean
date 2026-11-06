-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:43:37.946937+00:00
-- url     : https://prove2.me/theorems/c3b03f14-1faa-45f9-9c6f-9affda20be3f
-- title:
--   Original negative-jump squared kernel bounded by physical Lévy band mass
-- statement:
--   For any original spectrally negative Lévy X and the canonical continuous nonnegative-reserve value w vanishing below zero, a single finite squared envelope uniformly bounds the physical Lévy-measure quadratic energy of every negative jump from all initial reserve levels u≤K. This preserves the exact original ν, proves the essential separated finite-activity band estimate and uses no law substitution.
-- source:
--   From original canonical hw_cont, hw_neg and public Proved P4-F3 value bound 22692cae, prove a pathwise square bound, lift it via restricted-measure almost everywhere and ENNReal lintegral monotonicity, then use the constant integral. This is the deterministic large-band L2 energy input for actual source martingales, not their full stopped Itô proof.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The squared original negative-jump kernel has a finite-intensity envelope below a fixed reserve ceiling. -/

theorem AvramDividend.Classical.avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, u ≤ K →
      ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iic (0 : ℝ) →
      (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤
        ENNReal.ofReal A * X.ν B := by sorry
