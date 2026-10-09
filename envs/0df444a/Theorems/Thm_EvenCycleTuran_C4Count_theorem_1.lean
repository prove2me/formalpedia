-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_theorem_1
-- name    : EvenCycleTuran.C4Count.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:26:07.297988+00:00
-- url     : https://prove2.me/theorems/e11c37f5-fb70-463a-8de2-f2e4ebedf73b
-- title:
--   Theorem 1 (Bondy–Simonovits) — ex(n, C₂ₖ) = O(n^{1+1/k}) for k ≥ 2
-- statement:
--   Let $k\ge 2$. There is a constant $C$, depending only on $k$, such that every graph $G$ on $n$ vertices that contains no cycle of length $2k$ has
--
--   $$|E(G)|\le C\,n^{1+1/k}.$$
--
--   Equivalently, $\mathrm{ex}(n,C_{2k})=O(n^{1+1/k})$. This is the classical even-cycle theorem of Bondy and Simonovits, cited in the paper as Theorem 1. In the proof of Theorem 11 it shows that the number of fat $C_4$'s, which is at most a constant times $|E(G)|$, is $o(n^2)$.
--
--   **Formalization Note** The $O(\cdot)$ is written with an explicit constant $C$ chosen before $n$ and $G$; since the edge count of a graph on $0$ or $1$ vertices is $0$, the bound for all $n$ is equivalent to the bound for large $n$. The exponent is a real power.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 2, Theorem 1 (Bondy, Simonovits [6])

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- Theorem 1 (Bondy–Simonovits), p. 2: for `k ≥ 2`, ex(n, C₂ₖ) = O(n^{1+1/k}). The constant
`C` depends only on `k` and is chosen before `n` and the graph. -/
theorem theorem_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (cycleGraph (2 * k)).Free G →
        (#G.edgeFinset : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) + 1 / (k : ℝ)) := by sorry

end EvenCycleTuran.C4Count
