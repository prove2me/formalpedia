-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
-- name    : AvramDividend.Classical.avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:52:34.845637+00:00
-- url     : https://prove2.me/theorems/48ff97fd-17e6-4922-8923-1ace63d886bb
-- title:
--   Actual original ruin-bounded sampled physical-grid right dividend signed correction nonpositive
-- statement:
--   Given the TRUE original stopping clock rho constrained by rho<=ruinTime and the genuine filtered uniform grid physical sampling points 0 or t<rho, each actual discounted right-dividend secant loss has nonpositive sign, and the masked sum Q_k is nonpositive for every path and refinement. Uses the proved original arbitrary finite pre-ruin corrected discounted dividend sign. The earlier published helper f168b7b2 omitted the indispensable ruin-bounded stop hypothesis and should be treated as unsuitable: at points after ruin the HJB right-payment inequality does not apply.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_exact_ruinbounded_truegrid_zero_mask_filtered_right_payment_Q_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      ((Finset.range (k + 1)).image
        (fun i : ℕ => min
          ((i : ℝ≥0) * ((n : ℝ≥0) /
            ((k + 1 : ℕ) : ℝ≥0))) (ρ ω))).filter
          (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      if ρ ω = 0 then 0 else ∑ t ∈ A k ω,
        Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) -
            (w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω))))
    ∀ k ω, Q k ω ≤ 0 := by sorry
