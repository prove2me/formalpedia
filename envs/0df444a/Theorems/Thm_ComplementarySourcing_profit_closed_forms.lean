-- Prove2me | Theorems.Thm_ComplementarySourcing_profit_closed_forms
-- name    : ComplementarySourcing.profit_closed_forms
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:56.713007+00:00
-- url     : https://prove2.me/theorems/b7a732ce-5371-43df-820b-41ad5f5805c3
-- title:
--   (A4)–(A5), p.A5, at $n=2$ — closed forms of $\pi^{M*}_m$ and $\pi^{S*}_m$
-- statement:
--   Let $\mu>0$, $\alpha\ge0$, $\epsilon_0>0$, $0\le\sigma\le\epsilon_0$ and $r\mu\ge3\epsilon_0+\sigma$, with $x_1,x_2,\pi_1,\pi_2,k$ as in Proposition 2 and $w^M=(\epsilon_k-x_k)/(\mu(1+\alpha x_k)^2)$. Let $A_1=\tfrac12\epsilon_1+\tfrac12\epsilon_2$ and $A_2=\epsilon_2$. At every equilibrium of Model (M) and of Model (S),
--
--   $$\pi^{M*}_m=(r-w^M)\mu A_k-\tfrac12x_k^2,$$
--
--   $$\pi^{S*}_m=w^M\mu A_k-\tfrac12\cdot\tfrac12\Big(\frac{\epsilon_k-x_k}{1+\alpha x_k}\Big)^2-\tfrac12\cdot\tfrac12\Big(\frac{(\epsilon_2-x_k)^+}{1+\alpha x_k}\Big)^2.$$
--
--   These are the two expressions compared in the proof of Theorem 2: the second mover keeps the first mover's price margin but bears its effort cost realization by realization.
--
--   Differences from the source:
--   - encoding: general n, p_i → n = 2, p_1 = p_2 = ½, ϵ_1 = ϵ0 + σ, ϵ_2 = ϵ0 − σ; reason: the substitution the page prescribes on p.A11 for the proof of Theorem 2; general n is not an item of this mission
--   - encoding: the sums Σ_{i≤k} and Σ_{i=k+1}^{n̂}, with ϵ_{n̂+1} < x_k ≤ ϵ_n̂ → one term with ϵ_k − x_k and one term with max (ε₂ − x_k) 0; reason: at n = 2 the term i = 1 has ϵ_k, and the term i = 2 is present exactly when x_k ≤ ϵ_2, in which case its numerator is ϵ_2 − x_k
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
--   - reading: 0 ≤ σ ≤ ϵ0, with σ/ϵ0 and the optimal price meaningful → 0 < ε₀; reason: at ϵ0 = 0 demand is 0 at every price, so the printed unique optimum and the ratio σ/ϵ0 lose their meaning
--   - encoding: x_1, x_2 as "the unique value" of Lemma 3 → reals x₁, x₂ with the predicates IsEffortCandidate1/2 as hypotheses; reason: Lemma 3 proves each predicate has exactly one solution, so the same numbers are meant
--   - encoding: index k ∈ {1, 2} → k : Fin 2 given by smallestMaxIndex, with x_k = ![x₁, x₂] k; reason: the paper's indices 1, 2 are 0, 1; same value of k
--   - encoding: π^{M∗}, π^{S∗} named through "the smallest index k" → every equilibrium of each model; reason: the equilibrium is unique (Propositions 2 and 3), so no instance changes
--   - encoding: the second mover's response x*(·|ϵ) → an arbitrary strategy s with IsFollowerStrategy; reason: the page's best response as a map; by Lemma 2 its values are determined on the feasible moves and the two states
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), eqs. (A4)–(A5), p.A5; definitions of A_i, p.A1, and n̂, p.A2; n = 2 by the proof of Theorem 2, p.A11

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelM_game
import Definitions.Def_ComplementarySourcing_ModelM_supplierProfit
import Definitions.Def_ComplementarySourcing_ModelS_game
import Definitions.Def_ComplementarySourcing_ModelS_manufacturerProfit
import Definitions.Def_ComplementarySourcing_IsEffortCandidate1
import Definitions.Def_ComplementarySourcing_IsEffortCandidate2
import Definitions.Def_ComplementarySourcing_candidateProfit1
import Definitions.Def_ComplementarySourcing_candidateProfit2
import Definitions.Def_ComplementarySourcing_smallestMaxIndex
import Definitions.Def_ComplementarySourcing_riskLevel
import Definitions.Def_ComplementarySourcing_weightedRisk

namespace ComplementarySourcing

/-- **(A4)–(A5)** at `n = 2`, `p₁ = p₂ = ½`: `π^{M∗}_m = (r − w^M) µ A_k − ½ x_k²` and
`π^{S∗}_m = w^M µ A_k − ½ Σ_{i=1}^{k} p_i ((ϵ_k − x_k)/(1 + αx_k))² − ½ Σ_{i=k+1}^{n̂} p_i ((ϵ_i − x_k)/(1 + αx_k))²`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), eqs. (A4)–(A5), p.A5 (PDF 33).

**Formalization Note.** `n̂` satisfies `ϵ_{n̂+1} < x_k ≤ ϵ_n̂` (p.A2). At `n = 2` the two sums are the
terms `i = 1` and `i = 2`: the term `i = 1` always has `ϵ_k`, and the term `i = 2` is present exactly
when `x_k ≤ ϵ₂` and has `ϵ₂`, which the positive part `max (ϵ₂ − x_k) 0` encodes (it is also the
`i = 2 ≤ k` term when `k = 2`, since then `x_k ≤ ϵ₂`). -/
theorem profit_closed_forms {μ α r ε₀ σ x₁ x₂ π₁ π₂ xk wk xM wM xS wS : ℝ} {k : Fin 2}
    {sM sS : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ) (hσ : σ ≤ ε₀)
    (hx₁ : IsEffortCandidate1 α ε₀ σ x₁) (hx₂ : IsEffortCandidate2 α ε₀ σ x₂)
    (hπ₁ : π₁ = candidateProfit1 μ α r ε₀ σ x₁) (hπ₂ : π₂ = candidateProfit2 μ α r ε₀ σ x₂)
    (hk : k = smallestMaxIndex π₁ π₂) (hxk : xk = ![x₁, x₂] k)
    (hwk : wk = wholesaleCandidate μ α (riskLevel ε₀ σ k) xk)
    (hr : r * μ ≥ 3 * ε₀ + σ)
    (hM : (ModelM.game μ α r ε₀ σ).IsEquilibrium sM (xM, wM))
    (hS : (ModelS.game μ α r ε₀ σ).IsEquilibrium sS (xS, wS)) :
    ModelM.manufacturerProfit μ α r ε₀ σ xM wM (sM (xM, wM)) =
        (r - wk) * μ * weightedRisk ε₀ σ k - 1 / 2 * xk ^ 2 ∧
      ModelS.manufacturerProfit μ α r ε₀ σ xS wS (sS (xS, wS)) =
        wk * μ * weightedRisk ε₀ σ k
          - 1 / 2 * (1 / 2 * ((riskLevel ε₀ σ k - xk) / (1 + α * xk)) ^ 2)
          - 1 / 2 * (1 / 2 * (max (ε₀ - σ - xk) 0 / (1 + α * xk)) ^ 2) := by sorry

end ComplementarySourcing
