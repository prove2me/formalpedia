-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
-- name    : AvramDividend.Classical.avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:09:24.874871+00:00
-- url     : https://prove2.me/theorems/3218fa8e-269a-44e4-aaf9-995a294e9752
-- title:
--   Actual right-continuous-filtration adapted original pre-ruin discounted dividend single atom is L1 and L2
-- statement:
--   For the genuine original spectrally negative Levy source X of unbounded variation with nondegenerate Gaussian coefficient, any nonnegative discounted right-dividend payment at deterministic s made strictly before an original ruin-bounded stopped time is measurable in the original right-continuous filtration at s, nonnegative, integrable and square-integrable. Establish via the true original finite-grid mass first and second moment theorems for the singleton mesh. This is the actual predictable physical weight for the Gaussian future increment L1 bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_square_L1
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n s : ℝ≥0) (hsn : s ≤ n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    let H : Ω → ℝ := fun ω =>
      if s < ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (rightLimit D s ω - D s ω)
      else 0
    Measurable[𝓕.rightCont s] H ∧
      Integrable H P ∧
      Integrable (fun ω => (H ω)^2) P ∧
      (∀ ω, 0 ≤ H ω) := by sorry
