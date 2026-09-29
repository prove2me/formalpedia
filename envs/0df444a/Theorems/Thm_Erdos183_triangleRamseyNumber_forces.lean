-- Prove2me | Theorems.Thm_Erdos183_triangleRamseyNumber_forces
-- name    : Erdos183.triangleRamseyNumber_forces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:16:10.226694+00:00
-- url     : https://prove2.me/theorems/d16d8321-afc7-4da6-9cca-ca53d98d510c
-- title:
--   The triangle Ramsey number forces a monochromatic triangle
-- statement:
--   For every $k$, the value $R_k$ itself forces a monochromatic triangle on $k$ colours. Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle.
--
--   Because $R_k$ is defined as an infimum over the set of forcing values, this states that the infimum is attained — the set of forcing $n$ is nonempty (guaranteed by the recursive upper bound) and upward closed, so its least element is itself a forcing value.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L324-L326

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Data.Nat.Lattice

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.triangleRamseyNumber_forces (k : ℕ) :
    ForcesMonochromaticTriangle (triangleRamseyNumber k) k := by sorry
