-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_2
-- name    : BimatrixStableSet.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:49.306208+00:00
-- url     : https://prove2.me/theorems/96e34962-4fcf-4e45-942c-add1b251ac5a
-- title:
--   Theorem 2 — endpoints of almost completely labeled paths have opposite index (corrected: $d\ge1$)
-- statement:
--   Let $Z$ be a labeled polytope of dimension $d\ge1$, and let $h\in[d]$. If two different vertices are the endpoints of an $h$-almost completely labeled path, then they are completely labeled and
--
--   $$
--   \mathrm{index}(z)=-\mathrm{index}(w).
--   $$
--
--   Hence every completely labeled vertex has index $+1$ or $-1$, half of the completely labeled vertices have index $+1$, and the other half, including $0$, have index $-1$.
--
--   This is Shapley's index theorem. It is the source of the stable-set bound.
--
--   Differences from the source:
--   - correction: any labeled polytope → a labeled polytope of dimension $d\ge1$; reason: for $d=0$ the point $0$ is the only completely labeled vertex and has index $-1$, so the two halves are unequal
--   - encoding: the endpoints of an $h$-almost completely labeled path → two different vertices of degree one joined by a walk in the subgraph of $h$-almost completely labeled edges; reason: the proof of Theorem 1 describes this subgraph, which consists of paths and cycles
--   - encoding: half of the completely labeled vertices → the sets of completely labeled vertices of index $+1$ and $-1$ have equal `Set.encard`, and every completely labeled vertex has index $\pm1$; reason: same content
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 2, p.10; display (7)

import Mathlib
import Definitions.Def_BimatrixStableSet_LabeledPolytope

namespace BimatrixStableSet

/-- Theorem 2, p.10 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): for a labeled polytope,
the endpoints of any `h`-almost completely labeled path are completely labeled vertices of opposite
index. Hence, half of the completely labeled vertices have index `+1` and the other half, including
`0`, have index `-1`.

**Formalization Note.** The hypothesis `0 < d` corrects the printed statement: for `d = 0` the single
point `0` is the only completely labeled vertex and has index `-1`, so the two halves differ. The
index is that of display (7), with the sign `(-1)^(d+1)`. -/
theorem theorem_2 {d k : ℕ} (hd : 0 < d) (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d)
    (hC : IsLabeledPolytope C) :
    (∀ (h : Fin d) (z w : (labeledSystem C).vertices (labeledSystem C).carrier),
      IsAlmostPathEnds C ℓ h z w →
        IsCompletelyLabeled C ℓ z ∧ IsCompletelyLabeled C ℓ w ∧
        index C ℓ z = - index C ℓ w) ∧
    (∀ z ∈ (labeledSystem C).vertices (labeledSystem C).carrier, IsCompletelyLabeled C ℓ z →
      index C ℓ z = 1 ∨ index C ℓ z = -1) ∧
    {z ∈ (labeledSystem C).vertices (labeledSystem C).carrier |
        IsCompletelyLabeled C ℓ z ∧ index C ℓ z = 1}.encard =
      {z ∈ (labeledSystem C).vertices (labeledSystem C).carrier |
        IsCompletelyLabeled C ℓ z ∧ index C ℓ z = -1}.encard ∧
    IsCompletelyLabeled C ℓ 0 ∧ index C ℓ 0 = -1 := by sorry

end BimatrixStableSet
