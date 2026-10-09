-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_upper_bound
-- name    : EvenCycleTuran.C4Count.upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:17.886624+00:00
-- url     : https://prove2.me/theorems/d6fd5ea6-2c0b-47f2-82d5-7ed48f58d066
-- title:
--   Proof of Theorem 11, p. 12 — every C₂ₖ-free graph has at most (1+o(1))(k−1)(k−2)n²/4 four-cycles
-- statement:
--   Let $k\ge 2$. There is a function $\varepsilon(n)\to 0$, depending only on $k$, such that for all sufficiently large $n$ every graph $G$ on $n$ vertices containing no cycle of length $2k$ satisfies
--
--   $$\mathcal N(C_4,G)\le (1+\varepsilon(n))\,\frac{(k-1)(k-2)}{4}\,n^2 .$$
--
--   This is the upper half of Theorem 11, obtained by splitting the copies of $C_4$ into non-fat ones (at most $\binom{k-1}2\binom n2$) and fat ones ($O(n^{1+1/k})$).
--
--   **Formalization Note** $\mathcal N(C_4,G)$ is the number of unlabelled copies (`copyCount`). The $o(1)$ is a sequence $\varepsilon$ chosen before $n$ and $G$, uniform over all $C_{2k}$-free graphs on $n$ vertices. At $k=2$ the right side is $0$, i.e. a $C_4$-free graph has no $C_4$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 12, §4.1, proof of Theorem 11 (upper bound)

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- §4.1, p. 12, upper bound: every C₂ₖ-free graph on `n` vertices has at most
(1 + o(1))(k−1)(k−2)n²/4 copies of C₄; the o(1) depends only on `k`. -/
theorem upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n), (cycleGraph (2 * k)).Free G →
        (G.copyCount (cycleGraph 4) : ℝ) ≤
          (1 + ε n) * (((k : ℝ) - 1) * ((k : ℝ) - 2) / 4 * (n : ℝ) ^ 2) := by sorry

end EvenCycleTuran.C4Count
