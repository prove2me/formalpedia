-- Prove2me | Theorems.Thm_BlockCycleRotation_lower_order_le
-- name    : BlockCycleRotation.lower_order_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:46.693461+00:00
-- url     : https://prove2.me/theorems/a0eb5a8b-18a3-439e-93a2-90f1ca011b58
-- title:
--   The lower-order part of the main term
-- statement:
--   For $m,d>0$,
--   $$\sum_{\substack{(a,a') \text{ coprime} \\ d\,a(a+a') \le m}} \frac{d\,m}{a+a'} \le \left(\sqrt{\tfrac{m-1}{d}}+1\right) d\,m .$$
--
--   The bulk condition forces $a \le \sqrt{m/d}$, so the outer index runs over at most $\sqrt{(m-1)/d}+1$ values, and for each the inner sum over $a'$ telescopes against $a+a' \ge a$. This is the term that contributes $O(m^{3/2}\sqrt d)$ to the local form of Lemma 19.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1533-L1584

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.lower_order_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)) := by sorry
