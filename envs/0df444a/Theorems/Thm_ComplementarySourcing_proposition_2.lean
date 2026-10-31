-- Prove2me | Theorems.Thm_ComplementarySourcing_proposition_2
-- name    : ComplementarySourcing.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:59.967469+00:00
-- url     : https://prove2.me/theorems/bad12493-0b18-4eab-b359-dad9859f9bef
-- title:
--   Proposition 2, p.13 — the manufacturer's optimal decisions and profit
-- statement:
--   Let $\mu>0$, $\alpha\ge0$, $\epsilon_0>0$, $0\le\sigma\le\epsilon_0$ and $r\mu\ge3\epsilon_0+\sigma$. Let $x_1,x_2$ be as in Lemma 3, and define
--
--   $$\pi_1=\Big(r-\frac{\epsilon_1-x_1}{\mu(1+\alpha x_1)^2}\Big)\mu\epsilon_0-\tfrac12x_1^2,\qquad\pi_2=\Big(r-\frac{\epsilon_2-x_2}{\mu(1+\alpha x_2)^2}\Big)\mu\epsilon_2-\tfrac12x_2^2.$$
--
--   Let $k$ be the smallest index in $\{1,2\}$ with $\pi_k=\max\{\pi_1,\pi_2\}$. Then, against any best-responding supplier strategy:
--
--   1. the manufacturer's optimal decision in Model (M) is exactly $(x^M_m,w^M)=\Big(x_k,\dfrac{\epsilon_k-x_k}{\mu(1+\alpha x_k)^2}\Big)$;
--   2. $x^M_m\le\epsilon_0$;
--   3. the manufacturer's optimal expected profit is $\pi^{M*}_m=\pi_k=\max\{\pi_1,\pi_2\}$.
--
--   This solves Model (M).
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
--   - reading: 0 ≤ σ ≤ ϵ0, with σ/ϵ0 and the optimal price meaningful → 0 < ε₀; reason: at ϵ0 = 0 demand is 0 at every price, so the printed unique optimum and the ratio σ/ϵ0 lose their meaning
--   - reading: the printed "=" for the optimal decision → iff: (x, w) is an equilibrium with s exactly when it is the printed pair; reason: "the" optimal decisions: the printed pair is a maximizer and the only one
--   - encoding: x_1, x_2 as "the unique value" of Lemma 3 → reals x₁, x₂ with the predicates IsEffortCandidate1/2 as hypotheses; reason: Lemma 3 proves each predicate has exactly one solution, so the same numbers are meant
--   - encoding: index k ∈ {1, 2} → k : Fin 2 given by smallestMaxIndex, with x_k = ![x₁, x₂] k; reason: the paper's indices 1, 2 are 0, 1; same value of k
--   - encoding: the second mover's response x*(·|ϵ) → an arbitrary strategy s with IsFollowerStrategy; reason: the page's best response as a map; by Lemma 2 its values are determined on the feasible moves and the two states
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Proposition 2, p.13; proof p.A11 and Proposition A1, pp.A2–A5

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelM_game
import Definitions.Def_ComplementarySourcing_IsEffortCandidate1
import Definitions.Def_ComplementarySourcing_IsEffortCandidate2
import Definitions.Def_ComplementarySourcing_candidateProfit1
import Definitions.Def_ComplementarySourcing_candidateProfit2
import Definitions.Def_ComplementarySourcing_smallestMaxIndex
import Definitions.Def_ComplementarySourcing_riskLevel

namespace ComplementarySourcing

/-- **Proposition 2** (Optimal Manufacturer Effort): if `rµ ≥ 3ϵ₀ + σ`, the manufacturer's optimal
decisions are `(x_k, (ϵ_k − x_k)/(µ(1 + αx_k)²))`, moreover `x^M_m ≤ ϵ₀`, and the manufacturer's optimal
expected profit is `π_k = max{π₁, π₂}`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Proposition 2, p.13 (PDF 13).

**Formalization Note.** `x₁`, `x₂` are reals pinned by Lemma 3. The `↔` says that, against any best
responding supplier strategy `s`, the pair `(x_k, w_k)` is feasible and optimal and is the only
optimal pair; uniqueness is the reading of the printed "=". -/
theorem proposition_2 {μ α r ε₀ σ x₁ x₂ π₁ π₂ xk wk : ℝ} {k : Fin 2} {s : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ) (hσ : σ ≤ ε₀)
    (hx₁ : IsEffortCandidate1 α ε₀ σ x₁) (hx₂ : IsEffortCandidate2 α ε₀ σ x₂)
    (hπ₁ : π₁ = candidateProfit1 μ α r ε₀ σ x₁) (hπ₂ : π₂ = candidateProfit2 μ α r ε₀ σ x₂)
    (hk : k = smallestMaxIndex π₁ π₂) (hxk : xk = ![x₁, x₂] k)
    (hwk : wk = wholesaleCandidate μ α (riskLevel ε₀ σ k) xk)
    (hr : r * μ ≥ 3 * ε₀ + σ)
    (hs : (ModelM.game μ α r ε₀ σ).IsFollowerStrategy s) :
    (∀ xm w, (ModelM.game μ α r ε₀ σ).IsEquilibrium s (xm, w) ↔ xm = xk ∧ w = wk) ∧
      xk ≤ ε₀ ∧
      ModelM.manufacturerProfit μ α r ε₀ σ xk wk (s (xk, wk)) = ![π₁, π₂] k ∧
      ![π₁, π₂] k = max π₁ π₂ := by sorry

end ComplementarySourcing
