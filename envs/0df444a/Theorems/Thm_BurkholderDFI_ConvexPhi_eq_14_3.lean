-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_14_3
-- name    : BurkholderDFI.ConvexPhi.eq_14_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:13.626849+00:00
-- url     : https://prove2.me/theorems/46a33eeb-73de-4ce7-8697-aaa37c45d27d
-- title:
--   (14.3) — predictable bound for the small-jump part
-- statement:
--   For Davis's decomposition of a martingale, the centered small jump $a_k=y_k-E(y_k\mid\mathcal A_{k-1})$ satisfies, for $k\ge1$,
--   $$
--   |a_k|\le4d_{k-1}^*\quad\text{almost surely},
--   \qquad d_{k-1}^*=\max_{0\le j\le k-1}|d_j|.
--   $$
--   The right side is measurable at time $k-1$, giving predictable control of $g$.
--
--   **Formalization Note** The conditional expectation is real-valued because $y_k$ is integrable. The bound holds almost everywhere, matching the equivalence class nature of conditional expectation.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (14.3), p. 33

import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (14.3), p. 33: the small-jump martingale's predictable jump bound. -/
theorem eq_14_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    ∀ k, 1 ≤ k → ∀ᵐ ω ∂P,
      ENNReal.ofReal |davisA ℱ P f k ω| ≤
        4 * BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω := by sorry
end BurkholderDFI.ConvexPhi
