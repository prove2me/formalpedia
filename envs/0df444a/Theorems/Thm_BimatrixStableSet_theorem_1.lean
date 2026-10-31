-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_1
-- name    : BimatrixStableSet.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:40.70443+00:00
-- url     : https://prove2.me/theorems/f219346e-0d14-429f-ba8c-9272df32c4ff
-- title:
--   Theorem 1 — a labeled polytope has an even number of completely labeled points (corrected: $d\ge1$)
-- statement:
--   Let $Z$ be a labeled polytope of dimension $d\ge1$ (Definition 2). Then the set of completely labeled points of $Z$ is finite, and its cardinality is even.
--
--   This is the parity argument behind the Lemke–Howson algorithm: the number of Nash equilibria of a non-degenerate game is odd.
--
--   Differences from the source:
--   - correction: any labeled polytope → a labeled polytope of dimension $d\ge1$; reason: for $d=0$ and $k=0$ the single point of $\mathbb R^0$ is a labeled polytope with exactly one completely labeled point, and the proof picks a label $h\in[d]$ (counterexample proved in the verification file)
--   - reading: "$C$ without redundant inequalities" → no inequality of (5) is redundant; reason: the proof of Theorem 1 says "no inequality is redundant"; the two agree because the inequalities $-z_i\le0$ are never redundant when $0$ is a vertex
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 1, p.9

import Mathlib
import Definitions.Def_BimatrixStableSet_LabeledPolytope

namespace BimatrixStableSet

/-- Theorem 1, p.9 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): any labeled polytope has
an even number of completely labeled points.

**Formalization Note.** The hypothesis `0 < d` corrects the printed statement. For `d = 0`, the only
labeled polytope is the single point of `ℝ⁰` with `k = 0`, which is one completely labeled point. The
proof on p.9 chooses a label `h ∈ [d]`, so it assumes `d ≥ 1`. Finiteness of the set of completely
labeled points is part of the claim. -/
theorem theorem_1 {d k : ℕ} (hd : 0 < d) (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d)
    (hC : IsLabeledPolytope C) :
    ∃ s : Finset (Fin d → ℝ),
      (s : Set (Fin d → ℝ)) = {z | IsCompletelyLabeled C ℓ z} ∧ Even s.card := by sorry

end BimatrixStableSet
