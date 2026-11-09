-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_theorem_1_1
-- name    : BipHamCount.Deterministic.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:48:56.629941+00:00
-- url     : https://prove2.me/theorems/d695a0b8-53d2-4457-8678-572a6dde9d21
-- title:
--   Theorem 1.1 — exact deterministic bipartite Hamiltonian-cycle count in O(1.9526ⁿ)
-- statement:
--   There is a constant $C>0$, fixed before every input size and graph, such that for every natural number $n$ and every bipartite digraph $D$ on $n$ vertices, the fixed countHamCycles program returns the exact number $h(D)$ of directed Hamiltonian cycles and, when started at zero cost, satisfies
--   $$\operatorname{output}(\mathrm{countHamCycles}(D))=h(D),\qquad \operatorname{cost}(\mathrm{countHamCycles}(D))\le C\left(\frac{19526}{10000}\right)^n.$$
--   The input is just Boolean adjacency; no colouring is supplied. The program discovers one itself. The statement includes odd $n$, empty and singleton inputs, disconnected graphs and unequal colour-class sizes. A directed digon counts once. This is the paper's full exact-count theorem and numerical base, about a concrete deterministic program.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - encoding: directed Hamiltonian cycles, with the permutation-successor bijection on p.6 → single-cycle permutations with support equal to the full vertex set; counts zero for n≤1 and counts a directed digon once; reason: this is exactly the stated successor bijection on loopless nondegenerate inputs; the paper does not discuss n≤1
--   - reading: k=αn/2 with α=0.60909 used as an integer index → α=60909/100000 and kOf m=floor(60909m/100000), where n=2m; reason: an integer threshold is required by the valid-set DP; floor preserves the exponential bounds up to polynomial factors, including finitely many small m
--   - reading: time of the algorithm in §4 → charged bit operations of the fixed program; integer arithmetic costs (size|a|+size|b|+1)², with charged subset, table, loop and buffer operations; reason: the counter is generic; the reused Work definition supplies no unit-cost arithmetic assumption here; this accounts conservatively for integers of polynomial bit length
--   - encoding: given a bipartite digraph, with the balanced-side setting of §2 → input only adjacency on Fin n; charged stack DFS finds a colouring, with zero returned for empty or unequal-side inputs; reason: a Hamiltonian cycle alternates between equal sides and spans a connected graph; these preprocessing cases are necessary for the stated all-input theorem and cost only polynomial time
--   - encoding: time O(1.9526^n) → one positive real constant C quantified before n and adjacency, with charged cost at most C(19526/10000)^n; reason: this expresses the exact base without an instance-dependent constant or a hidden polynomial factor
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Theorem 1.1, p. 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Theorem 1.1 p.2, algorithm §4 pp.6–9, at full strength.
The fixed program discovers its own colouring. Every n and every bipartite digraph
are covered, including odd n, unequal sides and disconnected graphs. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      IsBipartiteDigraph adj →
        ((countHamCycles n adj).run 0).1 = hamCount adj ∧
        (((countHamCycles n adj).run 0).2 : ℝ) ≤ C * (19526/10000 : ℝ)^n := by sorry

end BipHamCount.Deterministic
