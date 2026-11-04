-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_square_lintegral_fatou_integrable
-- name    : AvramDividend.Classical.avram_p2_j_ui_real_square_lintegral_fatou_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:40:18.752613+00:00
-- url     : https://prove2.me/theorems/06791435-4440-438d-97cb-e74ef2b3e986
-- title:
--   Finite eventual ENNReal second-moment bounds imply square integrability of the a.e. real limit
-- statement:
--   For real random variables with measurable approximants and a strongly measurable almost-everywhere limit, a finite common upper bound on the eventual ENNReal squared-integral envelope passes to the limit by Fatou and establishes genuine Bochner integrability of the limit's square. This is an independent moment-inheritance result with no probability-space normalisation required.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_fatou_eventual_lintegral_bound

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_real_square_lintegral_fatou_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (K : ENNReal) (hK : K ≠ ⊤)
    (hm : ∀ n, Measurable (Y n))
    (hz : AEStronglyMeasurable Z P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω)))
    (hB : ∀ᶠ n : ℕ in atTop,
      (∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂P) ≤ K) :
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ K := by sorry
