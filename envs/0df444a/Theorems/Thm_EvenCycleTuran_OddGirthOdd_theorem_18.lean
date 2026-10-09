-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthOdd_theorem_18
-- name    : EvenCycleTuran.OddGirthOdd.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:25:10.699005+00:00
-- url     : https://prove2.me/theorems/d205299f-eeb6-4012-b24e-9937025e2118
-- title:
--   Theorem 18 — Ω(n^{1+1/(2k+2)}) = ex(n, C_{2l+1}, 𝒞_{2l} ∪ {C_{2k+1}}) = O(n²) for k > l ≥ 2
-- statement:
--   Let $k > l \ge 2$ be integers, and let $\mathrm{ex}(n, C_{2l+1}, \mathcal C_{2l} \cup \{C_{2k+1}\})$ be the maximum number of copies of the cycle $C_{2l+1}$ in a graph on $n$ vertices that contains no cycle of length $3, 4, \dots, 2l$ and no cycle of length $2k+1$. Then, as $n \to \infty$ with $k, l$ fixed,
--
--   $$\Omega\big(n^{1+\frac{1}{2k+2}}\big) = \mathrm{ex}\big(n, C_{2l+1}, \mathcal C_{2l} \cup \{C_{2k+1}\}\big) = O(n^2).$$
--
--   That is, there are constants $c, C > 0$ (depending on $k$ and $l$) such that for all sufficiently large $n$, $c\, n^{1 + 1/(2k+2)} \le \mathrm{ex}(n, C_{2l+1}, \mathcal C_{2l} \cup \{C_{2k+1}\}) \le C n^2$.
--
--   This is the odd-cycle counterpart of Theorem 17: when the additional forbidden cycle has odd length $2k+1$ instead of even length $2k$, the paper proves only a quadratic upper bound (and conjectures that the truth is sub-quadratic).
--
--   **Formalization Note** Both bounds are stated, as `Asymptotics.IsBigO` along `atTop`: $n^{1+1/(2k+2)} = O(\mathrm{ex})$ and $\mathrm{ex} = O(n^2)$. The forbidden family is every cycle length in $\{3, \dots, 2l\}$ together with $2k+1$. Copies are unlabelled. The abstract's "for $l > k \ge 2$" is a misprint; the theorem on pp. 7 and 28 has $k > l \ge 2$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 7, Theorem 18 (restated and proved pp. 28–29)

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthOdd_Setting

open Filter Asymptotics

namespace EvenCycleTuran.OddGirthOdd

/-- Theorem 18, p. 7 (restated p. 28): for `k > l ≥ 2`,
`Ω(n^{1+1/(2k+2)}) = ex(n, C_{2l+1}, 𝒞_{2l} ∪ {C_{2k+1}}) = O(n²)`. -/
theorem theorem_18 (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) + 1 / (2 * (k : ℝ) + 2))) =O[atTop]
        (fun n : ℕ => (exCyc n (SimpleGraph.cycleGraph (2 * l + 1))
          (Set.Icc 3 (2 * l) ∪ {2 * k + 1}) : ℝ)) ∧
    (fun n : ℕ => (exCyc n (SimpleGraph.cycleGraph (2 * l + 1))
          (Set.Icc 3 (2 * l) ∪ {2 * k + 1}) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) := by sorry

end EvenCycleTuran.OddGirthOdd
