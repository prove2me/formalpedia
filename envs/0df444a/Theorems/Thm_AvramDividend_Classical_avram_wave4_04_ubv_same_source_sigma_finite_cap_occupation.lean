-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:51:13.474963+00:00
-- url     : https://prove2.me/theorems/cc500549-ba08-47b0-b5c0-07c7a9bb40f3
-- title:
--   Original controlled UBV Lévy reserve has zero cap occupation for each fixed sigma-finite time measure before ruin
-- statement:
--   For the original unbounded-variation spectrally negative Lévy process X and the actual increasing adapted dividend path D, assume the source pre-ruin cap bound U_s≤c for all sample paths and all s before ruin. For every deterministic sigma-finite measure μ on nonnegative time, for P-almost every original sample path the controlled reserve U_t is strictly below the finite cap at μ-almost every positive surviving time. This is a real Fubini occupation statement on the same joint X,D filtration, including Gaussian and infinite-jump-activity UBV laws. It uses the genuinely proved fixed-terminal Lévy drawdown, source conditional cap logic, joint measurability of the actual controlled reserve and ruin time, and a Fubini swap. In particular, a Lebesgue time measure (when supplied on NNReal) is eligible. It does NOT imply zero mass for random path-dependent dividend Stieltjes measures, so it does not settle cap local-time/regulator payment terms or the full stopped Itô-Meyer inequality.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; corrected UBV target 429e17ca-5528-40b5-b593-7c03973d0706. Directly invokes Proved adapted fixed-time strict cap reserve 6f35bc03-dcf7-4cce-8358-6160ba421d27; Proved original-X joint time-state measurable d55462c3-decf-40f0-9aff-439d356324d9; Proved original-D predictable a4ef06a5-5b73-4d29-8e89-4a60aa82c3c5; Proved ruin-time measurable bbfbecf4-7dfc-4812-84f3-8644c2b40b85; pinned Mathlib predictable sigma inclusion and Fubini. The source hCap exactly instantiates the pre-ruin cap range already derived in the main corrected proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c) :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        riskProcess X x D t ω < c := by sorry
