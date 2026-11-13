-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_positive_ruin_stopped_contact_source_L1_limit
-- name    : AvramDividend.Classical.avram_bva_a22_original_positive_ruin_stopped_contact_source_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:46:23.22133+00:00
-- url     : https://prove2.me/theorems/8836ee25-1cf9-43aa-ab5b-b711c81d2279
-- title:
--   Actual original BVA96 positive-ruin clipped contact cash vanishes in expected value on the prescribed strict uniform horizon
-- statement:
--   For the actual original spectrally negative Lévy process, original admissible dividend control, positive real horizon and literal BVA96 uniform physical mesh width, the precise last ruin-or-horizon clipped Stieltjes cash supported strictly between stopped time minus width and stopped time has expectation tending to zero. The theorem uses BVA61, whose stopped real-payment integral is source identical, and retains the correct exclusion of the endpoint cash atom. It applies to the actual positive-ruin crossing child while also holding on all paths; it does not claim the marked jump residual, whole stopped C1 ledger or arbitrary spatial error L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_positive_ruin_stopped_contact_source_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun m => T / ((m : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ m)
          ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    Tendsto (fun m => ∫ ω, Contact m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
