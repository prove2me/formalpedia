-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_theorem_3_6
-- name    : BetterKMedian.LMPGreedy.theorem_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:59.393919+00:00
-- url     : https://prove2.me/theorems/75f84e3e-23ac-41bd-83ac-932e2031ec81
-- title:
--   Theorem 3.6 — for $\gamma\in[1,1.224]$ the factor-revealing program with $\beta_\gamma$ is at most $2-(\gamma-1)^2$ for all $n\ge1$
-- statement:
--   For every $\gamma\in[1,1.224]$ and every $n\ge1$, every feasible point of the factor-revealing program of Definition 3.2 with $\beta_\gamma(\alpha,d)=[\alpha-\gamma d]^+$ has objective at most $2-(\gamma-1)^2$.
--
--   Differences from the source:
--   - encoding: variables d_j, f, r_{j,k} for 1 ≤ j ≤ k ≤ n + 1 (Definition 3.2) → functions `d : ℕ → ℝ`, `r : ℕ → ℕ → ℝ` and `f : ℝ`, constraints only on the paper's 1-based ranges; values outside them occur in no constraint and not in the objective; reason: same feasible points restricted to the index ranges
--   - encoding: "is upper-bounded by 2 − (γ − 1)² for all n ≥ 1" → `FRBoundedBy (betaGamma γ) (2 - (γ - 1) ^ 2)`: every feasible point for every n ≥ 1 has objective ≤ 2 − (γ − 1)²; reason: no supremum is formed; same claim
--   - encoding: γ ∈ [1, 1.224] → `1 ≤ γ` and `γ ≤ 1224 / 1000` (real); reason: same interval
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Theorem 3.6, printed p. 15 (PDF 17); restated and proved p. 42 (PDF 44)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_FRProgram

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Theorem 3.6** (Buhai et al. 2026, printed p. 15, PDF 17; restated p. 42, PDF 44). For
`γ ∈ [1, 1.224]`, the factor-revealing program of Definition 3.2 with
`β_γ(α, d) = [α − γ · d]⁺` is upper-bounded by `2 − (γ − 1)²` for all `n ≥ 1`. -/
theorem theorem_3_6 (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 1224 / 1000) :
    FRBoundedBy (betaGamma γ) (2 - (γ - 1) ^ 2) := by sorry

end BetterKMedian.LMPGreedy
