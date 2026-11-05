-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_live_grid_expected_budget_of_source_mean
-- name    : AvramDividend.Classical.avram_p3_bv_original_live_grid_expected_budget_of_source_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:28:37.940944+00:00
-- url     : https://prove2.me/theorems/3c364269-ae79-4110-a99e-7dd5a1ec4dbc
-- title:
--   Actual original closed Stieltjes cash and true survival terminal expected grid bound from signed cap-linear source mean
-- statement:
--   On the original probability space, a single almost-sure strict live final clock permits all earlier grid cells. The real integral of physical closed-interval discounted dividend cash plus the true postpayment w terminal is bounded by the real integral of w(initial capital) whenever the fully expanded original cap-linear source grid correction is integrable with nonpositive expectation. This isolates the precise stochastic source expectation needed to close a physical stopped-grid verification.
-- source:
--   Source-exact application of Proved dc7eeb89 genuine physical grid accounting plus Mathlib integral_mono_ae and integral_add. Source signed-mean, integrability and ae live-clock remain explicit premises.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Expected original physical finite-grid verification: the actual closed
   Stieltjes cash and postpayment w terminal are bounded whenever the
   fully displayed cap-linear source correction has nonpositive mean. -/

theorem AvramDividend.Classical.avram_p3_bv_original_live_grid_expected_budget_of_source_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hLive : ∀ᵐ ω ∂P, (u n : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t =>
      x + X.X t ω - rightLimit D t ω
    let Z : Ω → ℕ → ℝ := fun ω i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    let CashTerm : Ω → ℝ := fun ω =>
      E (u n) * w (Y ω (u n)) +
        (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
    let Source : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) +
          E (u i) * (V (Z ω i) - V (Y ω (u i))))
    Integrable CashTerm P →
      Integrable Source P →
      Integrable (fun _ : Ω => w x) P →
      (∫ ω, Source ω ∂P) ≤ 0 →
      (∫ ω, CashTerm ω ∂P) ≤
        (∫ _ : Ω, w x ∂P) := by sorry
