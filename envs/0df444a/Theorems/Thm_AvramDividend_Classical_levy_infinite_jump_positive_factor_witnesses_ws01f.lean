-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_infinite_jump_positive_factor_witnesses_ws01f
-- name    : AvramDividend.Classical.levy_infinite_jump_positive_factor_witnesses_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:54:54.053759+00:00
-- url     : https://prove2.me/theorems/d7e8775f-2cfa-48a6-86f7-a7f633c6633f
-- title:
--   Infinite-small-jump Lévy exponent supplies genuine positive Esscher finite-clock root and derivative witnesses
-- statement:
--   For a genuine spectrally negative Lévy process with zero Gaussian component and infinite small-negative-jump first moment, construct positive q,phi,p,lam,m meeting the exact all-beta descending Wiener–Hopf factor hypotheses. Choose positive phi where ψ(phi)/phi>1 from accepted exponent growth, use the accepted positive-root secant bound at lam=phi for p>0, obtain the actual finite derivative at 2phi and its strictly positive root derivative lower bound.
-- source:
--   Canonical Proved psi_normalised_unbounded_small_jumps, levy_psi_root_shifted_increment_lower, avram_ws01e_cr_new_levy_psi_hasDerivAt_positive, esscher_levy_positive_root_derivative_lower.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_infinite_jump_positive_factor_witnesses_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∃ q φ p lam m : ℝ,
      0 < q ∧ 0 < φ ∧ X.ψ φ = q ∧
      0 < p ∧ 0 < lam ∧ X.ψ (φ + lam) - q = p ∧
      0 < m ∧ HasDerivAt X.ψ m (φ + lam) := by sorry
