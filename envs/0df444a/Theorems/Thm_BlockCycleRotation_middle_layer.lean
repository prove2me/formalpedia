-- Prove2me | Theorems.Thm_BlockCycleRotation_middle_layer
-- name    : BlockCycleRotation.middle_layer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:03.403002+00:00
-- url     : https://prove2.me/theorems/c372a292-a218-4b40-80c0-51a448e329a8
-- title:
--   The middle estimation layer: summing over pairs
-- statement:
--   For $m,d>0$,
--   $$\sum_{\substack{(a,a') \text{ coprime} \\ d\,a^2 < m}} \left( d\,a + \frac{2m}{a} \right)(1+\log m) \le \left(\sqrt{\tfrac{m-1}{d}}+1\right) \cdot 3m\,(1+\log m).$$
--
--   Summing the per-pair bounds of Lemmas 16 and 18 over the admissible pairs. The constraint $d a^2 < m$ caps the number of admissible $a$ by $\sqrt{(m-1)/d}+1$, and for each the sum over $a'$ contributes the bracketed factor.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1044-L1060

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.middle_layer {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m)) := by sorry
