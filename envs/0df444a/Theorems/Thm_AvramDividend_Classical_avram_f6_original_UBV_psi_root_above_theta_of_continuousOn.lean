-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_psi_root_above_theta_of_continuousOn
-- name    : AvramDividend.Classical.avram_f6_original_UBV_psi_root_above_theta_of_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:31:40.724663+00:00
-- url     : https://prove2.me/theorems/130ab718-469c-4d87-93d7-8ff5bebdf62f
-- title:
--   Original UBV Levy positive Laplace root above arbitrary growth θ from compact ψ continuity
-- statement:
--   The authentic original UBV Lévy positive root at any q and real compact-interval continuity of ψ imply for any θ there are actual λ>max(0,θ) and p>0 with ψ(λ)=p. Explicit compact source continuity, no Gaussian assumption, source genuine ψ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_psi_root_above_theta_of_continuousOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (θ : ℝ)
    (hψCont : ContinuousOn X.ψ (Icc (0 : ℝ) (max θ 0))) :
    ∃ p lam : ℝ, 0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by sorry
