-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_eq_1
-- name    : EvenCycleTuran.EvenCount.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:00.800255+00:00
-- url     : https://prove2.me/theorems/b80475aa-b5d8-4372-83de-2cccd7a33fb9
-- title:
--   (1), p. 9 — in a C_{2k}-free graph ½ Σ_{a≠b} C(f(a,b), 2) ≤ (1+o(1))(k−1)(k−2)n²/4
-- statement:
--   Let $k\ge 2$. There is a function $\varepsilon(n)\to0$, depending only on $k$, such that for all sufficiently large $n$ every $C_{2k}$-free graph $G$ on $n$ vertices satisfies
--   $$\frac12\sum_{\{a,b\},\,a\neq b}\binom{f(a,b)}{2}\le(1+\varepsilon(n))\frac{(k-1)(k-2)}{4}n^2,$$
--   where $f(a,b)$ is the number of common neighbours of $a$ and $b$ and the sum runs over unordered pairs of distinct vertices.
--
--   By the $C_4$ identity the left-hand side is the number of 4-cycles of $G$, so this is the upper bound of Theorem 11 ($\mathrm{ex}(n,C_4,C_{2k})=(1+o(1))\frac{(k-1)(k-2)}{4}n^2$). It controls the quadratic part of $\sum f^2$ in the proof of the upper bound of Theorem 10.
--
--   **Formalization Note** The function $\varepsilon$ is chosen before $n$ and before $G$. At $k=2$ the right-hand side is $0$, and the statement says that a $C_4$-free graph has no pair with two common neighbours.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, eq. (1)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph Filter Topology

theorem eq_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (cycleGraph (2 * k)).Free G →
        (1 / 2 : ℝ) * ∑ p ∈ offDiagPairs (Fin n), ((codegPair G p).choose 2 : ℝ) ≤
          (1 + ε n) * (((k : ℝ) - 1) * ((k : ℝ) - 2) / 4 * (n : ℝ) ^ 2) := by sorry

end EvenCycleTuran.EvenCount
