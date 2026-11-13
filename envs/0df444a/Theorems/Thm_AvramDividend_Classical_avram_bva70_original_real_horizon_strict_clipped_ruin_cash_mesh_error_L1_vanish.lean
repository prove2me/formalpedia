-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
-- name    : AvramDividend.Classical.avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:29:12.415456+00:00
-- url     : https://prove2.me/theorems/04e27c57-89b2-4c02-b625-130fe3f3a987
-- title:
--   Original arbitrary finite real-horizon ruin-clipped strict discounted cash mesh error is integrable and vanishes in mean
-- statement:
--   For the original spectrally negative Levy process and any admissible dividend process, clip the actual ruin time to an arbitrary finite real horizon T bounded by a positive integer n. The discounted strict physical-cell cash-error term with gap n/(m+2) and exact Stieltjes contact tail on (min(ruin,T)-gap,min(ruin,T)) is L1 at each mesh row and converges to zero in expected value. This extends the integer-stop original BVA67 to real T using the proved stopping clock BVA69 and generic stopped-mesh error BVA66, without finite-activity or global-generator-L1 assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem AvramDividend.Classical.avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0)) :
    let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ)) := by sorry
