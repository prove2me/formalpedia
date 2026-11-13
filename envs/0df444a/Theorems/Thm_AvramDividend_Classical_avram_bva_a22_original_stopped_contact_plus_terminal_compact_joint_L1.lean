-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_contact_plus_terminal_compact_joint_L1
-- name    : AvramDividend.Classical.avram_bva_a22_original_stopped_contact_plus_terminal_compact_joint_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:50:49.260197+00:00
-- url     : https://prove2.me/theorems/eda16730-9da6-42ff-bb57-9ff418cd7fc7
-- title:
--   Original BV stopped ruin-contact Stieltjes and compactly masked last-terminal positive error have a common integrable vanishing-mean envelope
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy X, admissible singular dividend D, positive real horizon and prescribed uniform physical grid, combine two independently proved source-exact error terms: the actual ruin-or-horizon contact Stieltjes cash in the last strict open interval, and the positive discounted full-T postpayment terminal omitted strip on original paths with both endpoints in a fixed strict compact reserve band and nonnegative horizon reward. Assuming only row integrability of the latter explicit compactly masked error, show that the sum is integrable at each row and its expectation tends to zero. The exact original BVA97 supplies contact L1 and mean convergence, and A22 compact terminal theorem supplies the terminal convergence. Retains original process, filtration, cash convention and correct surviving terminal. Spatial boundary excursions and compensated C1 raw-to-H discrepancy remain separate tasks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_stopped_contact_plus_terminal_compact_joint_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDs : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Contact : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ n)
              ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ∈ Icc c d ∧
         (x + X.X S ω - rightLimit D S ω) ∈ Icc c d ∧
          0 ≤ w (x + X.X S ω - rightLimit D S ω) then
        max (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, Integrable (Err m) P) →
    (∀ m, Integrable (fun ω => Contact m ω + Err m ω) P) ∧
    Tendsto (fun m => ∫ ω, Contact m ω + Err m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
