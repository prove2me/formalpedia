-- Prove2me | Theorems.Thm_FASTournament_fasMengerian_of_strong_components
-- name    : FASTournament.fasMengerian_of_strong_components
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:19.378171+00:00
-- url     : https://prove2.me/theorems/5053de08-ef49-47e6-9625-c82488fdfa74
-- title:
--   Reduction to strong tournaments: FAS Mengerian strong components give an FAS Mengerian tournament
-- statement:
--   Let $T$ be a finite tournament. If, for every strong component $S$ of $T$, the subtournament $T[S]$ is FAS Mengerian, then $T$ is FAS Mengerian.
--
--   This is the step "we may assume that $T$ is strong" in the proof of (i) ⇒ (iii) of Theorem 1.2.
--
--   **Formalization Note** The strong component of $v$ is the set of vertices $u$ such that $u$ is reachable from $v$ and $v$ from $u$.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - reading: "Clearly, we may assume that T is strong" (a reduction step of the proof) → if every strong component induces an FAS Mengerian subtournament, then T is FAS Mengerian; reason: this is what the reduction asserts: implication (i) ⇒ (iii) for T follows from it for the strong components, which are Möbius-free subtournaments of T
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26 ("It remains to prove implication (i) ⇒ (iii). Clearly, we may assume that T is strong.")

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_FASMengerian
import Definitions.Def_FASTournament_induce

namespace FASTournament

/-- **Reduction to strong tournaments.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26: "It remains to prove implication (i) ⇒ (iii). Clearly, we
may assume that T is strong."

If every strong component of a finite tournament `T` induces a FAS Mengerian subtournament, then
`T` is FAS Mengerian.

**Formalization Note.** The strong component of `v` is the set of vertices `u` with `u`
reachable from `v` and `v` reachable from `u`; it is induced as a digraph on that subtype. -/
theorem fasMengerian_of_strong_components {V : Type*} [Fintype V] (T : Digraph V)
    (hT : IsTournament T)
    (h : ∀ v : V, FASMengerian
      (induce T {u | Relation.ReflTransGen T.Adj u v ∧ Relation.ReflTransGen T.Adj v u})) :
    FASMengerian T := by sorry

end FASTournament
