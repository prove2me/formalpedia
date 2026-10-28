-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
-- name    : AvramDividend.Classical.scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:32:33.404385+00:00
-- url     : https://prove2.me/theorems/097a29e5-ff86-4f5d-b65b-f952540cc19d
-- title:
--   Superlinear Lévy exponent implies zero scale origin for every nonnegative discount
-- statement:
--   This is a necessary zero-boundary input for root-connected unbounded_scale_C1_zero_discount_core (8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d), which reduces scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q. It extends the already Proved scaleFunction_origin_zero_of_superlinear_psi (effa0ac0-898d-4af8-a4f6-6c59968d96b4) from strictly positive discount q to nonnegative q, importantly including q=0. The Lean proof uses the independently Proved generic Laplace-origin-zero lemma and the same superlinear-growth estimates, replacing strict positivity of q by nonnegativity throughout. This theorem is independently provable and does not import the open zero-discount C1 core.
-- source:
--   Proved scaleFunction_origin_zero_of_superlinear_psi and laplace_origin_zero_of_normalised_small, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hgrowth : ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ) :
    W 0 = 0 := by sorry
