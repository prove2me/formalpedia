-- Prove2me | Theorems.Thm_ForgetAlt_theorem_1_1
-- name    : ForgetAlt.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:36.589914+00:00
-- url     : https://prove2.me/theorems/fbd2fa1e-af3c-4ac8-9e73-fd3de3aa1f20
-- title:
--   Theorem 1.1: any vertex-disjoint double path algorithm in a DAG yields vertex-disjoint shortest augmenting paths in $O(T(n,m)+m\log n)$, preserving maximality
-- statement:
--   Suppose an algorithm $\mathcal A$ outputs, for every instance $(H,E_c)$ of the double path problem, a set of vertex-disjoint double paths in time $O(T(|V(H)|,|E(H)|+|E_c|))$. Then there is an algorithm $\mathcal B$ that, given a graph $G$ with $n$ vertices and $m$ edges and a matching $M$ of $G$, computes a set of vertex-disjoint shortest augmenting paths of $(G,M)$ in time
--
--   $$O\big(T(n,m)+m\log n\big).$$
--
--   Moreover, if $\mathcal A$ always outputs a maximal set of double paths, the same $\mathcal B$ outputs a maximal set of vertex-disjoint shortest augmenting paths.
--
--   Combined with an $O(m\log n)$ maximal double path algorithm and the Hopcroft–Karp phase bound, this gives an $O(m\sqrt n\log n)$ maximum matching algorithm whose correctness proof avoids blossoms.
--
--   Differences from the source:
--   - reading: “an algorithm … in O(·) time” → a program of the published word RAM EndStatement (step count), correct at every word width W ≥ b·(⌊log₂ size⌋ + 1); A is any such program and B is one program with constants b, C; reason: the paper's model is the word RAM with O(log n)-bit words; the hypothesis is about programs of the same machine, not an oracle
--   - reading: O(T(…)) and O(T(n, m) + m log n) → ≤ C_A·(T(N, |E(H)| + |E_c|) + 1) and ≤ C·(T̂(n, m) + m·⌊log₂ n⌋ + 1); reason: the + 1 only matters when the bound is 0
--   - reading: T(n, m) in the conclusion → T̂(n, m) = max{T(a, b) : a ≤ n, b ≤ m}; reason: B runs A on an instance with at most n vertices and at most m arcs plus bridges, so the paper presumes T nondecreasing; T̂ = T for every nondecreasing T
--   - encoding: an instance (H, E_c); a graph G with a matching M → the DPProblem and AugProblem input/output layouts; a DAG with nonrepeating arc and bridge lists; any graph on Fin n, isolated vertices allowed; reason: fixed word layouts; no condition beyond the problem statement
--   - reading: “if the algorithm ensures that D is maximal, A is also maximal” → if A also solves the maximal version within the same bound, then B solves the maximal version within the same bound; reason: the run is deterministic and its time is already bounded by the first hypothesis
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 1.1, printed pp.3–4 (PDF pp.4–5)

import Mathlib
import Definitions.Def_ForgetAlt_Machine

namespace ForgetAlt

open BergeMatching.Core

/-- **Theorem 1.1**, printed pp.3–4 (PDF pp.4–5). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Suppose that there exists an algorithm outputting a set `D` of vertex-disjoint double paths in
`O(T(|V(H)|, |E(H)| + |E_c|))` time for any instance `(H, E_c)`. Then there exists an algorithm
that, given a graph `G` with `n` vertices and `m` edges and a matching `M` of `G`, computes a set
`A` of vertex-disjoint shortest augmenting paths in `(G, M)` in `O(T(n, m) + m log n)` time. In
particular, if the algorithm ensures that `D` is maximal, `A` is also maximal."

**Formalization Note.** Algorithms are programs of the published word RAM `EndStatement`, time is
the number of steps. For every `T` and every program `A` that solves the double path problem on
every valid instance within `C_A·(T(N, |E(H)| + |E_c|) + 1)` steps (at every width
`W ≥ b_A·(⌊log₂ size⌋ + 1)`), there are one program `B` and constants `b, C` such that `B`
outputs vertex-disjoint shortest augmenting paths for every graph `G` on `Fin n` (isolated
vertices allowed) and matching `M` within `C·(T̂(n, m) + m·⌊log₂ n⌋ + 1)` steps, `T̂` the monotone
envelope of `T` (`= T` for nondecreasing `T`); and the same `B` outputs a maximal set whenever
`A`'s outputs are maximal. -/
theorem theorem_1_1 (T : ℕ → ℕ → ℕ) (A : List EndStatement.Instr) (bA CA : ℕ)
    (hA : DPRunsWithin false A bA
      (fun N I => CA * (T N (I.arcs.length + I.bridges.length) + 1))) :
    ∃ (B : List EndStatement.Instr) (b C : ℕ),
      AugRunsWithin false B b
        (fun n x => C * (Tenv T n x.edges.length + x.edges.length * Nat.log 2 n + 1)) ∧
      (DPRunsWithin true A bA (fun N I => CA * (T N (I.arcs.length + I.bridges.length) + 1)) →
        AugRunsWithin true B b
          (fun n x => C * (Tenv T n x.edges.length + x.edges.length * Nat.log 2 n + 1))) := by sorry

end ForgetAlt
