-- Prove2me | Theorems.Thm_Erdos183_triangleRamseyNumber_log_isTheta
-- name    : Erdos183.triangleRamseyNumber_log_isTheta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:18:59.155035+00:00
-- url     : https://prove2.me/theorems/3acf8e96-63f6-463c-8b24-bfd31e714dc6
-- title:
--   The order of growth: $\log R_k = \Theta(k \log k)$
-- statement:
--   As $k \to \infty$,
--
--   $$\log R_k \;=\; \Theta(k \log k).$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. Combining the superexponential lower bound with the factorial upper bound pins the growth of $\log R_k$ to within constant factors of $k \log k$.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2966-L2997

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.triangleRamseyNumber_log_isTheta :
    (fun k : ℕ => Real.log (triangleRamseyNumber k : ℝ))
      =Θ[atTop] (fun k : ℕ => (k : ℝ) * Real.log (k : ℝ)) := by sorry
