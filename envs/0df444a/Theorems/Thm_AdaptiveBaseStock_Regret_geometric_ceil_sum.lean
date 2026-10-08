-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_geometric_ceil_sum
-- name    : AdaptiveBaseStock.Regret.geometric_ceil_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:38.014981+00:00
-- url     : https://prove2.me/theorems/e2bc2a4f-d679-4e71-bac6-6a46cd0b44ea
-- title:
--   Lemma 12 — Σ_{k≤L} ρ^{⌈k^β⌉} ≤ Σ_{k≤L} ρ^{k^β} ≤ Γ(1/β)(1/β)/(ln(1/ρ))^{1/β}
-- statement:
--   For every $\rho \in (0,1)$, $\beta \in (0,1)$ and $L \ge 1$,
--   $$\sum_{k=1}^L \rho^{\lceil k^\beta\rceil} \le \sum_{k=1}^L \rho^{k^\beta} \le \frac{\Gamma(1/\beta)\,(1/\beta)}{(\ln(1/\rho))^{1/\beta}},$$
--   where $\Gamma(z) = \int_0^\infty w^{z-1} e^{-w}\,dw$ is the Gamma function.
--
--   The bound is uniform in $L$; it sums the geometrically decaying bias of the gradient estimates over cycles of length $\lceil k^\beta\rceil$.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Lemma 12, p. 25 (proof in Appendix A, p. 32)

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm

namespace AdaptiveBaseStock.Regret

/-- Lemma 12, p. 25: for `ρ, β ∈ (0, 1)` and `L ≥ 1`,
`Σ_{k=1}^L ρ^{⌈k^β⌉} ≤ Σ_{k=1}^L ρ^{k^β} ≤ Γ(1/β)(1/β) / (ln(1/ρ))^{1/β}`. -/
theorem geometric_ceil_sum (ρ β : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (L : ℕ) (hL : 1 ≤ L) :
    ∑ k ∈ Finset.Icc 1 L, ρ ^ cycleLen β k ≤ ∑ k ∈ Finset.Icc 1 L, ρ ^ ((k : ℝ) ^ β) ∧
    ∑ k ∈ Finset.Icc 1 L, ρ ^ ((k : ℝ) ^ β)
      ≤ Real.Gamma (1 / β) * (1 / β) / (Real.log (1 / ρ)) ^ (1 / β) := by sorry

end AdaptiveBaseStock.Regret
