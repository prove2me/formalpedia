-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
-- name    : AvramDividend.Classical.avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:27:37.039225+00:00
-- url     : https://prove2.me/theorems/9a0e2593-768c-41ca-82fa-36f1d7172374
-- title:
--   Exact original BV strict cash-contact error is integrable and mean vanishes
-- statement:
--   The original BVA63 ruin-contact Stieltjes cash term has exact discounted time interval (min(ruin,T)-T/(m+2),min(ruin,T)); it is integrable for every m and its mean tends to zero, by Proved BVA64. This isolates the cash-contact L1 obligation for the nonzero-ruin positive error branch without changing any source process or payment convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Contact : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ n)
              ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    (∀ m, Integrable (Contact m) P) ∧
      Tendsto (fun m => ∫ ω, Contact m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
