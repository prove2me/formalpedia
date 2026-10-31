-- Prove2me | Theorems.Thm_CompetitionComplexity_theorem_3
-- name    : CompetitionComplexity.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:19.893294+00:00
-- url     : https://prove2.me/theorems/b718d99b-859b-4d8f-bcea-c01fa5b593f1
-- title:
--   Theorem 3 — $(1+\varepsilon)A_m(F)\ge M_n(F)$ for all $F$ iff the program (1)–(4) has non-negative value
-- statement:
--   Let $\varepsilon\ge0$ and let $n,m$ be positive integers. Then
--   $$
--   (1+\varepsilon)A_m(F)\ge M_n(F)\quad\text{for every distribution } F
--   $$
--   if and only if the optimal value of the program
--   $$
--   \text{minimize}\ (1+\varepsilon)\sum_{i=0}^{m-1}\delta_i-\sum_{i=0}^{\infty}\Bigl(1-\Bigl(\frac{\delta_{i+1}}{\delta_i}\Bigr)^n\Bigr)\delta_i\quad\text{subject to (2)–(4)}
--   $$
--   is non-negative, where (2)–(4) require $\delta$ non-increasing, log-convex ($\delta_j^2\le\delta_{j-1}\delta_{j+1}$), $\delta_0=1$ and $\delta_j>0$.
--
--   This reduces the competition-complexity question, which quantifies over all distributions, to an optimization problem over sequences; Lemma 4 then solves that problem.
--
--   **Formalization Note** "The optimal value is non-negative" is stated as "the objective is non-negative at every feasible sequence", which is equivalent since the value is the infimum over the feasible set.
--
--   Differences from the source:
--   - encoding: Mₙ(F) a real number compared with (1 + ε)Aₘ(F) → Mₙ in [0, ∞] (ENNReal) compared with ENNReal.ofReal((1 + ε)Aₘ); reason: Mₙ(F) is finite and (1 + ε)Aₘ(F) ≥ 0 for every distribution, so the comparison is unchanged
--   - encoding: the optimal value of (1)–(4) is non-negative → the objective (1) is ≥ 0 at every δ satisfying (2)–(4); reason: the value is the infimum over the feasible set, so the two are equivalent; avoids Lean's junk sInf
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Theorem 3, p.7

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Definitions.Def_CompetitionComplexity_Distribution
import Definitions.Def_CompetitionComplexity_Program

open MeasureTheory
open CorreaThreshold.Adaptive (dpW)

namespace CompetitionComplexity

/-- **Theorem 3** (an equivalent optimization problem).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Theorem 3, p.7:
"Let ε ≥ 0, and let n and m be two positive integers. Then, we have (1+ε)Am(F) ≥ Mn(F) for every
distribution F if and only if the optimal value of the optimization problem (1)-(4) is non-negative."

**Formalization Note.** "The optimal value is non-negative" is stated as "the objective (1) is
non-negative at every feasible `δ`", which is equivalent (the value is the infimum over the feasible
set) and avoids Lean's junk `sInf`. -/
theorem theorem_3 (ε : ℝ) (hε : 0 ≤ ε) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ μ : Measure ℝ, IsDist μ → Mval μ n ≤ ENNReal.ofReal ((1 + ε) * dpW μ m)) ↔
      ∀ δ : ℕ → ℝ, Feasible δ → 0 ≤ objective ε n m δ := by sorry

end CompetitionComplexity
