-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_5
-- name    : BimatrixStableSet.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:47.644729+00:00
-- url     : https://prove2.me/theorems/1fa27c4f-9b22-4105-ad02-81ed28d0610d
-- title:
--   Lemma 5 — adjacent equilibrium vertices have opposite index
-- statement:
--   Let $(A,B)$ be a non-degenerate game with best-response polytopes $P$ and $Q$. If $(x,y)$ and $(x',y')$ are equilibria and $x,x'$ are adjacent in the graph of $P$, then
--
--   $$
--   \mathrm{index}(x,y)=-\mathrm{index}(x',y').
--   $$
--
--   Thus the equilibrium vertices of equal index form a stable set of the graph of $P$.
--
--   Differences from the source:
--   - encoding: the standing assumptions of the section, stated once → explicit hypotheses `HasBestResponsePolytopes A B` and `IsNondegenerate A B`; reason: same instances
--   - encoding: "belong to equilibria of opposite index" → the equilibria are given as hypotheses with $x,x'$ adjacent; reason: the partner of a vertex is unique, p.11
--   - encoding: the index for $Z=P\times Q$ as a labeled polytope → `equilibriumIndex`, display (7) with the $C$ of (6), reading only binding rows; reason: $P$ and $Q$ may have never-binding redundant rows under Lemma 3(c), which Definition 2 forbids; the determinant is the same
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 5, p.11; displays (6), (7)

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_LabeledPolytope

namespace BimatrixStableSet

variable {m n : ℕ}

/-- Lemma 5, p.11 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): any two equilibrium vertices
of `P` that are connected by an edge belong to equilibria of opposite index.

**Formalization Note.** The standing assumptions of §5 are hypotheses: the game is non-degenerate
and `P`, `Q` are polytopes. No irredundancy of the rows of `P` and `Q` is assumed. The index is
`equilibriumIndex`, display (7) with the `C` of display (6), which reads only binding rows. -/
theorem lemma_5 (A B : Matrix (Fin m) (Fin n) ℝ) (hPQ : HasBestResponsePolytopes A B)
    (hAB : IsNondegenerate A B) (x x' : Fin m → ℝ) (y y' : Fin n → ℝ)
    (hxy : IsEquilibrium A B x y) (hxy' : IsEquilibrium A B x' y')
    (hadj : (bestResponseP B).AdjIn (bestResponseP B).carrier x x') :
    equilibriumIndex A B x y = - equilibriumIndex A B x' y' := by sorry

end BimatrixStableSet
