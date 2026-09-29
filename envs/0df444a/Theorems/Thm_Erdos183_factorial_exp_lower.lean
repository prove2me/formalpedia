-- Prove2me | Theorems.Thm_Erdos183_factorial_exp_lower
-- name    : Erdos183.factorial_exp_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:16:41.145479+00:00
-- url     : https://prove2.me/theorems/5a664554-be34-47e5-a22c-457698d04a21
-- title:
--   Elementary lower bound $(s/e)^s \le s!$
-- statement:
--   For every positive integer $s$,
--
--   $$\left(\frac{s}{e}\right)^{s} \;\le\; s!.$$
--
--   This standard estimate — the easy half of Stirling's approximation — converts the factorial growth appearing in the construction into a clean exponential form.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L692-L707

import Definitions.Def_erdos183_core
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Real.StarOrdered

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.factorial_exp_lower (s : ℕ) (hs : 0 < s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by sorry
