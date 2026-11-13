-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva57_original_BV_physical_joint_cell_contact_L1_signed_grid
-- name    : AvramDividend.Classical.avram_bva57_original_BV_physical_joint_cell_contact_L1_signed_grid
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T12:20:15.517092+00:00
-- url     : https://prove2.me/theorems/0e56d7b6-7dfc-4ac1-bcbc-c1a2fa1b2451
-- title:
--   Original infinite-activity BV physical joint positive cell/contact L1 signed grid
-- statement:
--   On the original spectrally negative Lévy source and arbitrary admissible singular dividend strategy, construct the signed compensated-jump/HJB/Stieltjes grid correction N_m with nonpositive expectation. Prove the exact strict-horizon original cash plus surviving full-T postpayment reward is bounded by initial reward and N_m plus the two positive physical errors, and prove that the single expected sum of positive cell and ruin-contact errors tends to zero. The two components must be integrable and originate in the actual physical grid including infinite small-mark activity, time-zero right payments, and ruin contacts. The proved squeeze_zero and additivity of integral separate the joint estimate into the two separate limits required by bva43.
-- source:
--   Sound stronger source refinement of bva43; single joint L1 estimate rather than independently establishing two separate convergence statements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva57_original_BV_physical_joint_cell_contact_L1_signed_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ N ErrCell ErrContact : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable (fun ω => max (ErrCell m ω) 0) P) ∧
      (∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P) ∧
      (∀ m, ∀ᵐ ω ∂P, F m ω ≤ w x + N m ω +
        max (ErrCell m ω) 0 + max (ErrContact m ω) 0) ∧
      Tendsto (fun m =>
        ∫ ω, max (ErrCell m ω) 0 + max (ErrContact m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
