-- Prove2me | Theorems.Thm_Erdos183_erdos_183
-- name    : Erdos183.erdos_183
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:19:19.057779+00:00
-- url     : https://prove2.me/theorems/20fe567a-7ed5-460a-80f2-682ba4da33a1
-- title:
--   Erdős problem 183: $R_k^{1/k} \to \infty$
-- statement:
--   $$R_k^{1/k} \;\longrightarrow\; \infty \qquad (k \to \infty).$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. This is Erdős problem 183 in its original qualitative form: does the $k$-th root of the $k$-colour triangle Ramsey number tend to infinity? The affirmative answer follows from the explicit superexponential lower bound established by the palette construction.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L3035-L3040

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.erdos_183 :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by sorry
