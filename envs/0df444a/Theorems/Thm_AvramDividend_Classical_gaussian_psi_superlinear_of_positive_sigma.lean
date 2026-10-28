-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
-- name    : AvramDividend.Classical.gaussian_psi_superlinear_of_positive_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:36:29.162138+00:00
-- url     : https://prove2.me/theorems/c1392cb2-b5da-4f7e-b8e7-854fe3d2ee4f
-- title:
--   Positive Gaussian volatility makes the Lévy Laplace exponent superlinear
-- statement:
--   This exactly supplies the superlinear-growth premise of the newly published scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q (097a29e5-ff86-4f5d-b65b-f952540cc19d), allowing its conclusion W(0)=0 for q=0 in the Gaussian branch of the root-connected zero-discount C1 core 8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d. From the canonical Proved psi_quadratic_lower_from_compensated_negative_jumps, the exponent ψ(θ) is at least cθ+(σ²/2)θ²−J, with J fixed. Since σ>0, for any C and sufficiently large θ≥1 the positive quadratic term dominates Cθ+J. The proof is a bounded polynomial inequality using pinned Mathlib and one imported Proved theorem. No open core is imported.
-- source:
--   Proved psi_quadratic_lower_from_compensated_negative_jumps (97e86a26-c9f2-497c-92cb-e9f05afd2ff5), canonical Lévy-Khintchine representation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_lower_from_compensated_negative_jumps
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_psi_superlinear_of_positive_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : 0 < X.σ) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ := by sorry
