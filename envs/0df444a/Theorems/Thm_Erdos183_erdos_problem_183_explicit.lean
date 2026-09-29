-- Prove2me | Theorems.Thm_Erdos183_erdos_problem_183_explicit
-- name    : Erdos183.erdos_problem_183_explicit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:19:28.569203+00:00
-- url     : https://prove2.me/theorems/f049c5a7-8921-4399-b172-6087fa46d745
-- title:
--   Erdős problem 183, explicit form
-- statement:
--   The resolution of Erdős problem 183 in explicit form: for every $k \ge 2$,
--
--   $$\left(\frac{1}{6e^{38}} \cdot \frac{k^{1/3}}{\log k}\right)^{k} \;\le\; R_k,$$
--
--   and consequently
--
--   $$R_k^{1/k} \longrightarrow \infty.$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. The first conjunct is a superexponential lower bound with fully explicit constants; the second is the qualitative divergence Erdős asked about, which the first implies. This is the headline result of the formalisation.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L3042-L3051

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.erdos_problem_183_explicit :
    (∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ)) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop atTop := by sorry
