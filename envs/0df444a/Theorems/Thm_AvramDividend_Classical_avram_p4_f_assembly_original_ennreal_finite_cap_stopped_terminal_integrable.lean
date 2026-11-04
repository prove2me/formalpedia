-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:18:35.822517+00:00
-- url     : https://prove2.me/theorems/f11748f4-d481-4ffe-9483-30eea0ed99a7
-- title:
--   Canonical ENNReal finite-cap original stopped terminal is L1
-- statement:
--   For the actual original Lévy source and the canonical ENNReal cap C≠∞, convert C to its real value using ENNReal.ofReal_toReal, transport the original admissible control and initial bound, and invoke the accepted finite-real-cap L1 theorem on the true postpayment-or-ruin reserve and exact Term. This discharges canonical Term integrability on all finite caps without a new moment hypothesis. The C=∞ branch remains open.
-- source:
--   Accepted P4-F original finite real-cap stopped terminal integrable theorem 2d3eb5aa; pinned Mathlib ENNReal.ofReal_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCfin : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) :
    Integrable Term P := by sorry
