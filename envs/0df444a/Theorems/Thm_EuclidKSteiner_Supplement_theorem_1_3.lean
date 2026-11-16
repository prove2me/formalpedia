-- Prove2me | Theorems.Thm_EuclidKSteiner_Supplement_theorem_1_3
-- name    : EuclidKSteiner.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:58:51.376909+00:00
-- url     : https://prove2.me/theorems/0fc6506a-425c-4f9f-97ce-0a71a658b042
-- title:
--   Theorem 1.3 — continuous planar Euclidean $k$-Steiner tree with terminals on an $L\times L$ grid in $2^{O(k\log k)}(n+L)^{O(1)}$ time
-- statement:
--   Let $P_0,\dots,P_{n-1}$ be terminals in the plane $\mathbb R^2$ whose coordinates are integers in $\{0,\dots,L\}$, and let $k\ge1$ be an integer. For a finite point set $X$, write $w(\mathrm{MST}(X))$ for the total Euclidean length of a minimum spanning tree of $X$.
--
--   **Theorem.** There are a deterministic real-RAM program and a constant $C>0$ such that, on every such input, the program halts after $t$ steps with
--   $$t+1\le C\cdot 2^{C k\log_2(k+2)}\cdot(n+L+2)^{C}$$
--   and outputs a list $S$ of at most $k$ points of $\mathbb R^2$ with
--   $$w(\mathrm{MST}(P\cup S))\le w(\mathrm{MST}(P\cup S'))\quad\text{for every finite } S'\subseteq\mathbb R^2 \text{ with } |S'|\le k .$$
--
--   So continuous Euclidean $k$-Steiner tree, where Steiner points may be placed anywhere in the plane, is fixed-parameter tractable in $k$ on polynomially bounded integer grids; Theorem 1.4 shows that the dependence on $L$ cannot be removed unless FPT = W[1].
--
--   **Formalization Note** The real RAM is the published admissible `MatMulTimeLP.RealRAM`, as in the published goal. Input: $k, n, L$, then the coordinates; output: the number of Steiner points, then their coordinates. Terminal and Steiner point sets are images of lists, so repeated points collapse.
--
--   Differences from the source:
--   - generalization: "on an L × L integer grid" → every coordinate an integer in $\{0,\dots,L\}$; reason: the paper does not fix the grid; $\{0,\dots,L\}^2$ contains $\{0,\dots,L-1\}^2$ and $\{1,\dots,L\}^2$, so each reading is a special case, with the same bound.
--   - encoding: "2^{O(k log k)}(n + L)^{O(1)} time" → one constant $C$ before the input, $t+1\le C\,2^{Ck\log_2(k+2)}(n+L+2)^C$; reason: meaning of the $O(\cdot)$ bounds; $\log_2(k+2)$ keeps the exponent positive at $k=1$ and differs from $\log k$ by a constant factor for $k\ge2$.
--   - encoding: "time" → steps of the published admissible real RAM; reason: the paper's model (p.3).
--   - encoding: n terminals; the computed Steiner tree → an indexed sequence $P:\mathrm{Fin}\,n\to\mathbb R^2$ (repetitions allowed; the terminal set is its image) given as the reals $k,n,L$ and the $2n$ coordinates; the output is the list of at most $k$ Steiner points, whose optimality is stated against every finite $S'\subseteq\mathbb R^2$ with $|S'|\le k$; reason: input/output representation; an injective sequence is the source's set of $n$ terminals, with the same bound.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Theorem 1.3, p.3 (PDF p.5); restated p.33 (PDF p.35); proof §7, pp.33–38 (PDF pp.35–40)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Instance
import Definitions.Def_EuclidKSteiner_Supplement_GridLayout

set_option autoImplicit false

namespace EuclidKSteiner

namespace Supplement

/-- **Theorem 1.3 (continuous planar k-Steiner tree on a grid).** Bhore, Kisfaludi-Bak, Marx, Odak,
*Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256
75361687…), Theorem 1.3, p.3 (PDF p.5); restated p.33 (PDF p.35), proved in §7: "Given n terminals
on an L × L integer grid in the plane and an integer k ≥ 1, a minimum-length continuous Euclidean
k-Steiner tree can be found deterministically in 2^{O(k log k)}(n + L)^{O(1)} time." The problem
(§1, p.2): "Find a set S ⊆ ℝ^d with |S| ≤ k minimizing w(MST(P ∪ S))".

There are an admissible real-RAM program and a constant `C > 0` such that for every `k ≥ 1`, every
`L ≥ 0`, all terminals `P 0, …, P (n−1)` of the plane with integer coordinates in `{0, …, L}` and every
tape, the run on `gridLayout k L P` halts at a step `t` with
`t + 1 ≤ C · 2^{C·k·log₂(k+2)} · (n + L + 2)^C` and outputs a list `S` of at most `k` points of the
plane such that `w(MST(P ∪ S)) ≤ w(MST(P ∪ S'))` for every finite `S' ⊆ ℝ²` with `|S'| ≤ k`.

**Formalization Note**
* Machine: `MatMulTimeLP.RealRAM` restricted by `FewInnerTSP.Admissible`, as in the published goal.
* `k·log₂(k+2)` stands for `k log k` (positive at `k = 1`); `+ 2` keeps the base at least `2`.
* The grid is `{0, …, L}²` (see `OnGrid`); optimality is against every finite point set of the
  plane, not against a candidate set. The output lists the Steiner points themselves. -/
theorem theorem_1_3 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k L n : ℕ) (P : Fin n → E 2), 1 ≤ k → OnGrid L P →
      ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ,
        MatMulTimeLP.HaltsAt A (gridLayout k L P) ω t ∧
        (t : ℝ) + 1 ≤ C * (2 : ℝ) ^ (C * k * Real.logb 2 ((k : ℝ) + 2)) * ((n + L : ℝ) + 2) ^ C ∧
        ∃ S : List (E 2), S.length ≤ k ∧ OutputIs A (gridLayout k L P) ω t (encodePoints S) ∧
          ∀ S' : Finset (E 2), S'.card ≤ k →
            mstWeight (Finset.univ.image P ∪ S.toFinset) ≤ mstWeight (Finset.univ.image P ∪ S') := by sorry

end Supplement

end EuclidKSteiner
