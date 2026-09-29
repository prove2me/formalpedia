-- Prove2me | Theorems.Thm_Erdos183_triangleRamseyNumber_factorial_upper
-- name    : Erdos183.triangleRamseyNumber_factorial_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:16:20.409313+00:00
-- url     : https://prove2.me/theorems/3bcb699d-8e22-4adc-bf72-fb4698ad4e1f
-- title:
--   Factorial upper bound $R_k \le 4\,k!$
-- statement:
--   For every $k$,
--
--   $$R_k \;\le\; 4 \cdot k!.$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. This is the classical upper bound obtained by iterating the pigeonhole recursion $n \mapsto 1 + (k+1)n$ from the base case, and it supplies the upper half of the asymptotic $\log R_k = \Theta(k \log k)$.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L334-L362

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.NormNum.NatFactorial

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.triangleRamseyNumber_factorial_upper (k : ℕ) :
    triangleRamseyNumber k ≤ 4 * k.factorial := by sorry
