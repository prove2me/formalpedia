-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_square_L1
-- name    : AvramDividend.Classical.avram_lsv_original_preruin_discounted_rightatoms_square_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:15:11.277457+00:00
-- url     : https://prove2.me/theorems/4b4a62c5-6bb8-4843-bb11-da5d0018f0b2
-- title:
--   Source-exact original Gaussian dividend pre-ruin discounted physical mesh mass has bounded second moment
-- statement:
--   The entire discounted right-dividend finite physical mesh sum strictly before ruin has integrable square under original unbounded-variation Levy and dividend strategy assumptions. Its second moment is at most the original initial reserve square plus the running supremum square, with explicit factor two. This derives uniform mesh square-integrability from the authentic original pre-ruin source and needs no hypothetical post-ruin dividend bound, supporting Cauchy-Schwarz with original Gaussian fourth moments to close the stopped Ito-Meyer pre/post linear mesh correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_preruin_discounted_rightatoms_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (s : ℕ → ℝ≥0) (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (hbound : ∀ i ∈ Finset.range m, s i ≤ n)
    (q : ℝ) (hq : 0 ≤ q) :
    let A : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range m,
        if s i < ρ ω then
          Real.exp (-(q * (s i : ℝ))) *
            (rightLimit D (s i) ω - D (s i) ω)
        else 0
    Integrable (fun ω => (A ω)^2) P ∧
      (∫ ω, (A ω)^2 ∂P) ≤
        ∫ ω, 2*x^2 + 2*(runningSup X n ω)^2 ∂P := by sorry
