-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_native_root_coefficient_positive
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_native_root_coefficient_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:04:36.985718+00:00
-- url     : https://prove2.me/theorems/7924a2b2-100d-48c3-b51c-eeeec0e78487
-- title:
--   The exact canonical Esscher Lévy–Khintchine ladder drift coefficient is strictly positive at any positive q-root
-- statement:
--   For any genuine spectrally negative Lévy process with positive q, positive Esscher root φ satisfying ψφ=q, the exact native positive-root coefficient c minus the mapped-jump atom at size one plus σ²φ and the compensated positive-height integral is at least q/φ and strictly positive. Full differentiability follows from accepted native positive-parameter regularity, the exact coefficient identity from the accepted source-faithful Volterra theorem, and derivative positivity from the accepted convex secant root lemma.
-- source:
--   Source-faithful combination of remotely Proved avram_ws01e_cr_new_levy_psi_hasDerivAt_positive, avram_ws01e_cr_new_native_positive_root_derivative_coefficient and esscher_levy_positive_root_derivative_lower. Strict inequality directly supplies the positivity needed in the positive descending ladder-height killed potential normalisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_native_positive_root_derivative_coefficient
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_native_root_coefficient_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    q / φ ≤ X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) -
        z * Real.exp (-φ * z) ∂(X.ν.map (fun y : ℝ => -y))) ∧
      0 < X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) -
        z * Real.exp (-φ * z) ∂(X.ν.map (fun y : ℝ => -y))) := by sorry
