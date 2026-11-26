-- Prove2me | Theorems.Thm_Erdos1007_completeBipartiteGraph_three_three_unitDistance
-- name    : Erdos1007.completeBipartiteGraph_three_three_unitDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:18.066933+00:00
-- url     : https://prove2.me/theorems/7a16d38d-7edc-5745-8397-04c884a9ecfc
-- title:
--   Erdos1007: complete Bipartite Graph three three unit Distance
-- statement:
--   **Upper bound** for the dimension of `K₃,₃`: the complete bipartite graph on `3 + 3` vertices
--   admits an injective placement in `ℝ⁴` realising every edge as a unit segment (blueprint node
--   `lem:k33-dim`; Chaffee–Noble Lemma 3, attributed there to Erdős–Harary–Tutte).
--
--   With `r = 1/√2` the left part sits at `{(r, 0, 0, 0), (-r, 0, 0, 0), (0, r, 0, 0)}` and the right
--   part at `{(0, 0, r, 0), (0, 0, -r, 0), (0, 0, 0, r)}`; the squared distance of a cross pair is
--   `r² + r² = 1`.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartite.lean#L129-L133
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartite.lean#L129-L133

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartite
set_option autoImplicit false
@[expose] public section
open Erdos1007
public section

theorem Erdos1007.completeBipartiteGraph_three_three_unitDistance :
    ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4), Function.Injective f ∧
      ∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1 := by sorry
