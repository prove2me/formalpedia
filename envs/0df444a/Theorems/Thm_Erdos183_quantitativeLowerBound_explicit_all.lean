-- Prove2me | Theorems.Thm_Erdos183_quantitativeLowerBound_explicit_all
-- name    : Erdos183.quantitativeLowerBound_explicit_all
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:18:39.68544+00:00
-- url     : https://prove2.me/theorems/5dab4c5f-0003-4faf-9a5b-838aa87fe732
-- title:
--   Explicit superexponential lower bound for $R_k$
-- statement:
--   For every $k \ge 2$,
--
--   $$\left(\frac{1}{6e^{38}} \cdot \frac{k^{1/3}}{\log k}\right)^{k} \;\le\; R_k.$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. This is the explicit quantitative heart of the resolution of Erdős problem 183. Because the base $\frac{1}{6e^{38}} k^{1/3}/\log k$ tends to infinity with $k$, the bound is superexponential, and it immediately gives $R_k^{1/k} \to \infty$.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2752-L2790

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.quantitativeLowerBound_explicit_all :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ) := by sorry
