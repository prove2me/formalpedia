-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_lemma_16_1
-- name    : BurkholderDFI.ConvexPhi.lemma_16_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:04.424986+00:00
-- url     : https://prove2.me/theorems/746b9f8a-ed03-41e6-ba1e-cd52b2482040
-- title:
--   Lemma 16.1 — convex comparison for predictable projections
-- statement:
--   Let $z_1,z_2,\ldots$ be nonnegative measurable random variables on a filtered probability space. For any convex function $\Phi$ satisfying the moderate-growth conditions of §7, there is a constant $C>0$, depending only on its doubling constant, such that
--   $$
--   E\Phi\left(\sum_{k\ge1}E(z_k\mid\mathcal A_{k-1})\right)
--   \le C E\Phi\left(\sum_{k\ge1}z_k\right).
--   $$
--   This is the convexity estimate needed for the large-jump term in Theorem 15.1.
--
--   **Formalization Note** The $z_k$ are not assumed adapted. Extended nonnegative conditional expectations handle nonintegrable $z_k$ without assigning an artificial zero value.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 16.1, p. 34

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Lemma 16.1, p. 34: convex Φ comparison for sums and predictable projections. -/
theorem lemma_16_1 (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞),
        (∀ k, Measurable (z k)) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c → BurkholderDFI.SquareFnLp.IsConvexPhi Φ →
          (∫⁻ ω, Φ (∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω) ∂P) ≤
            (C : ℝ≥0∞) * ∫⁻ ω, Φ (∑' k : ℕ, z (k + 1) ω) ∂P := by sorry
end BurkholderDFI.ConvexPhi
