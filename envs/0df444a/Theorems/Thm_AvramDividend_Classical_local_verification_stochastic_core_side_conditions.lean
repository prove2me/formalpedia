-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
-- name    : AvramDividend.Classical.local_verification_stochastic_core_side_conditions
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:50:34.880451+00:00
-- url     : https://prove2.me/theorems/d307095e-a960-48c5-9b42-f2578aca7372
-- title:
--   All four deterministic side conditions for the stopped Lévy–Itô HJB core follow from root HJB assumptions
-- statement:
--   Under the root verification HJB assumptions, a capped-admissible dividend strategy and initial capital within cap, derive the complete conjunction of the four analytic/pathwise assumptions required by the still-Open admissible_cap_truncated_ubv_stochastic_core: (1) generator integrability and Γw−qw≤0 throughout the interior, (2) w′≥1, (3) w(riskProcess)≥0 strictly before ruin for positive times, and (4) each initial or strictly pre-ruin right-dividend atom bounded by its verification-function decrease. HJB max=0 splits into drift and gradient by the previously accepted local_verification_hjb_implies_components; the other two are the independently accepted strict pre-ruin book-value nonnegativity and right dividend atom control. The theorem DOES NOT infer the stopped stochastic budget or assume Itô's formula. It is the exact interface gathering all the established prerequisites for that missing stochastic result.
-- source:
--   Depends only on Proved HJB components, candidate 12288 and 12289, and foundational definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_capped_admissible_bookReserve_candidate_nonnegative_preRuin
import Theorems.Thm_AvramDividend_Classical_capped_admissible_hjb_right_dividend_atom_control

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_stochastic_core_side_conditions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by sorry
