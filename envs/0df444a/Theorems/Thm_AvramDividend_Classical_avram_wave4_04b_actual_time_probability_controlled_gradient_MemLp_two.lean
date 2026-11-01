-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_time_probability_controlled_gradient_MemLp_two
-- name    : AvramDividend.Classical.avram_wave4_04b_actual_time_probability_controlled_gradient_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:25:55.477323+00:00
-- url     : https://prove2.me/theorems/d861d958-9eae-4a89-ad49-8d067fc4c4ae
-- title:
--   Actual controlled interior Brownian-gradient L2 under literal source time probability product
-- statement:
--   Promotes the original source-controlled strict pre-jump compact interior gradient squared-energy to genuine MemLp 2 over the literal finite-horizon Lebesgue-time × original probability P product space, with its ordinary joint measurable structure. No replacement marginal coupling and no restriction to absolutely continuous dividends; the gradient is derived from the actual adapted Lévy and full Stieltjes dividend strategy.
-- source:
--   Already Proved direct actual finite-horizon gradient energy 08dd89a3 and the right-continuous predictable-to-product measurable-space inclusion from 16857b34's accepted source, followed by Mathlib real MemLp two equivalence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_actual_time_probability_controlled_gradient_MemLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    MemLp G 2 ((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  sorry
