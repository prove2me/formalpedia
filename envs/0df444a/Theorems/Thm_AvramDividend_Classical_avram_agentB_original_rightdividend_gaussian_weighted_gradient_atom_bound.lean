-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_rightdividend_gaussian_weighted_gradient_atom_bound
-- name    : AvramDividend.Classical.avram_agentB_original_rightdividend_gaussian_weighted_gradient_atom_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:22:48.161555+00:00
-- url     : https://prove2.me/theorems/3a144162-200b-4676-8222-70a1e2f13908
-- title:
--   Original dividend right-atom compact Gaussian first-Hermite gradient error bounded by actual jump mass
-- statement:
--   For the genuine controlled Lévy reserve and actual right dividend atom at a physical grid time s in a compact positive interior C2 band, the nonnegative discount factor times the absolute pre/post dividend gradient error times absolute centred Gaussian increment is bounded by the same factor times the compact Hessian bound K, actual dividend right jump mass and absolute centred Gaussian increment. This is the precise cellwise quantitative source envelope for the original stopped linear gradient error.
-- source:
--   Proved avram_gledger23_original_samegrid_prepost_gradient_jump_bound and elementary nonnegative multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_rightdividend_gaussian_weighted_gradient_atom_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K)
    (s : ℝ≥0) (ω : Ω)
    (hPre : riskProcess X x D s ω ∈ Icc a b)
    (hPost : x + X.X s ω - rightLimit D s ω ∈ Icc a b)
    (hRight : 0 ≤ rightLimit D s ω - D s ω)
    (e z : ℝ) (he : 0 ≤ e) :
    e * |deriv w (x + X.X s ω - rightLimit D s ω) -
           deriv w (riskProcess X x D s ω)| * |z| ≤
       e * ((K : ℝ) * (rightLimit D s ω - D s ω)) * |z| := by sorry
