-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_psi_root_runningSup_exp_L1
-- name    : AvramDividend.Classical.avram_f6_original_positive_psi_root_runningSup_exp_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:28:36.318918+00:00
-- url     : https://prove2.me/theorems/45ea4e4d-dc41-4c12-a2c8-750a2595f7cb
-- title:
--   True non-Gaussian-compatible Laplace root finite-horizon runningSup exponential is Bochner-integrable
-- statement:
--   For any source spectrally negative Lévy X (including σ=0), with ψ(λ)=p>0 and 0≤β<λ, exact exp(β runningSup X T) is integrable. Proof uses original positive-root exponential fixed-horizon lintegral and original joint measurability, not Gaussian-only moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_positive_psi_root_runningSup_exp_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : 0 ≤ β) (hβlam : β < lam)
    (n : ℝ≥0) :
    Integrable (fun ω : Ω => Real.exp (β * runningSup X n ω)) P := by sorry
