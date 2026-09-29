-- Prove2me | Theorems.Thm_Erdos183_triangleRamseyNumber_log_sharp_coefficients
-- name    : Erdos183.triangleRamseyNumber_log_sharp_coefficients
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:18:49.548118+00:00
-- url     : https://prove2.me/theorems/6c709911-84cc-43e4-aa99-5c91d2b3735f
-- title:
--   Sharp logarithmic coefficients: $\tfrac13 \le \liminf, \limsup \le 1$
-- statement:
--   For every $\varepsilon > 0$, for all sufficiently large $k$,
--
--   $$\left(\tfrac{1}{3} - \varepsilon\right) k \log k \;\le\; \log R_k \;\le\; (1 + \varepsilon)\, k \log k.$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. The upper coefficient comes from the factorial bound $R_k \le 4\,k!$ together with $\log k! \sim k \log k$; the lower coefficient $1/3$ comes from the $k^{1/3}$ in the explicit construction.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2792-L2877

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.triangleRamseyNumber_log_sharp_coefficients :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((1 / 3 : ℝ) - ε) * (k : ℝ) * Real.log (k : ℝ) ≤
            Real.log (triangleRamseyNumber k : ℝ) ∧
          Real.log (triangleRamseyNumber k : ℝ) ≤
            (1 + ε) * (k : ℝ) * Real.log (k : ℝ) := by sorry
