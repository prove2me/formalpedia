-- Prove2me | Theorems.Thm_Erdos183_exists_recursivePaletteStage
-- name    : Erdos183.exists_recursivePaletteStage
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:16:50.646498+00:00
-- url     : https://prove2.me/theorems/a5b7a72e-cd42-45f0-9d7c-0c2bd53a2ac5
-- title:
--   Existence of a recursive palette stage
-- statement:
--   For all $H, a, j$ with $2 \le H$, $2 \le a$ and $j \le H$, there exist an $n$ and an edge-colouring $C$ of $K_n$ by $j \cdot (a \cdot \text{saturatedMatrixRows}(H))$ colours such that:
--
--   1. $C$ is triangle-free;
--   2. every colour class of $C$ is $(j+1)$-colourable as a graph;
--   3. the pair $(n, \text{parameters})$ satisfies the growth bound $\text{PaletteGrowthBound}$.
--
--   This is the engine of the lower bound. It produces one stage of the recursive palette construction, carrying along both the triangle-freeness needed for the Ramsey bound and the colourability invariant needed to iterate, together with the quantitative control on how fast the vertex count grows.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2044-L2085

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.exists_recursivePaletteStage (H a j : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hj : j ≤ H) :
    ∃ (n : ℕ)
      (C : SimpleGraph.TopEdgeLabeling (Fin n)
        (Fin (j * (a * saturatedMatrixRows H)))),
      TriangleFree C ∧
        (∀ colour : Fin (j * (a * saturatedMatrixRows H)),
          (C.labelGraph colour).Colorable (j + 1)) ∧
        PaletteGrowthBound a (saturatedMatrixRows H) j n := by sorry
