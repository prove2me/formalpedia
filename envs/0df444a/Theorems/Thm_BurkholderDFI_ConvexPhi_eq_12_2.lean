-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_12_2
-- name    : BurkholderDFI.ConvexPhi.eq_12_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:56.439438+00:00
-- url     : https://prove2.me/theorems/692f63a0-97ae-4329-8be2-beb5d0256271
-- title:
--   (12.2) — square function under predictable jump control
-- statement:
--   Let $f$ be a martingale whose differences satisfy $|d_k|\le w_k$ almost surely, where each $w_k$ is measurable with respect to $\mathcal A_{k-1}$. Let $w^*=\sup_{k\ge1}w_k$. For every moderate-growth function $\Phi$ there is a constant $C>0$, depending only on its doubling constant, such that
--   $$
--   E\Phi(S(f))\le C E\Phi(f^*)+C E\Phi(w^*).
--   $$
--   The same $C$ multiplies both terms. This inequality controls the square function in the presence of predictable jump bounds.
--
--   **Formalization Note** The constant is chosen before the probability space, martingale, bounds, and $\Phi$. The bounds and expectations have extended nonnegative values, and the index-zero Mathlib extension is ignored by $d_k$, $S(f)$, and $f^*$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (12.2), §12, p. 31

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (12.2), p. 31: square function controlled by maximal function and predictable jumps. -/
theorem eq_12_2 (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f w : ℕ → Ω → ℝ),
        Martingale f ℱ P →
        (∀ k, 1 ≤ k → Measurable[ℱ (k - 1)] (w k)) →
        (∀ k, 1 ≤ k → ∀ᵐ ω ∂P, |BurkholderDFI.SquareFnLp.dseq f k ω| ≤ w k ω) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤
            (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P +
            (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn w ω) ∂P := by sorry
end BurkholderDFI.ConvexPhi
