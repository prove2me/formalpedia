-- Prove2me | Theorems.Thm_Erdos183_allColourPaletteRamsey_exponential_bound_sharp
-- name    : Erdos183.allColourPaletteRamsey_exponential_bound_sharp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:18:19.537821+00:00
-- url     : https://prove2.me/theorems/1b4e9f4d-9651-45c2-92ff-a41e9fd5d210
-- title:
--   Sharp exponential lower bound at every colour count
-- statement:
--   For every $k \ge \text{paletteColourCount}(3)$ there exists a stage $H \ge 3$ with
--
--   $$\text{paletteColourCount}(H) \le k < \text{paletteColourCount}(H+1) \qquad\text{and}\qquad \left(\frac{H}{e^{38}}\right)^{k} \le R_{k}.$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. This is the sharp form of the lower bound: rather than holding only for the special colour counts produced by the recursion, it holds at *every* $k$, by locating $k$ between consecutive stages and transferring the bound with the slow-growth estimates on the width parameters.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2556-L2592

import Definitions.Def_erdos183_core
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.allColourPaletteRamsey_exponential_bound_sharp (k : ℕ)
    (hk : paletteColourCount 3 ≤ k) :
    ∃ H : ℕ,
      3 ≤ H ∧
      paletteColourCount H ≤ k ∧
      k < paletteColourCount (H + 1) ∧
      ((H : ℝ) / Real.exp 38) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by sorry
