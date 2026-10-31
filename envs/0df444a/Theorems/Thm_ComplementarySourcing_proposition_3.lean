-- Prove2me | Theorems.Thm_ComplementarySourcing_proposition_3
-- name    : ComplementarySourcing.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:42.262371+00:00
-- url     : https://prove2.me/theorems/fbc5e35e-c0e0-4d0a-8bbd-21717a0c54bf
-- title:
--   Proposition 3, p.14 — the supplier's optimal decisions and the manufacturer's response
-- statement:
--   Let $\mu>0$, $\alpha\ge0$, $\epsilon_0>0$, $0\le\sigma\le\epsilon_0$ and $r\mu\ge\epsilon_1+2\epsilon_0$, with $x_1,x_2,\pi_1,\pi_2,k$ as in Proposition 2. Then, against any best-responding manufacturer strategy, the supplier's optimal decision in Model (S) is exactly
--
--   $$(x^S_s,w^S)=\Big(x_k,\ r-\frac{\epsilon_k-x_k}{\mu(1+\alpha x_k)^2}\Big).$$
--
--   Furthermore, for realized market risk $\epsilon=\epsilon_i$, $i=1,2$, the manufacturer's optimal effort at this decision is
--
--   $$x^S_m(x^S_s,w^S\mid\epsilon=\epsilon_i)=\begin{cases}0&\text{if }x^S_s\ge\epsilon_i,\\ \min\Big(\mu(r-w^S)(1+\alpha x^S_s),\ \dfrac{\epsilon_i-x^S_s}{1+\alpha x^S_s}\Big)&\text{if }x^S_s\le\epsilon_i.\end{cases}$$
--
--   This solves Model (S).
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
--   - reading: 0 ≤ σ ≤ ϵ0, with σ/ϵ0 and the optimal price meaningful → 0 < ε₀; reason: at ϵ0 = 0 demand is 0 at every price, so the printed unique optimum and the ratio σ/ϵ0 lose their meaning
--   - reading: the printed "=" for the optimal decision → iff: (x, w) is an equilibrium with s exactly when it is the printed pair; reason: "the" optimal decisions: the printed pair is a maximizer and the only one
--   - encoding: x_1, x_2 as "the unique value" of Lemma 3 → reals x₁, x₂ with the predicates IsEffortCandidate1/2 as hypotheses; reason: Lemma 3 proves each predicate has exactly one solution, so the same numbers are meant
--   - encoding: index k ∈ {1, 2} → k : Fin 2 given by smallestMaxIndex, with x_k = ![x₁, x₂] k; reason: the paper's indices 1, 2 are 0, 1; same value of k
--   - encoding: the second mover's response x*(·|ϵ) → an arbitrary strategy s with IsFollowerStrategy; reason: the page's best response as a map; by Lemma 2 its values are determined on the feasible moves and the two states
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Proposition 3, p.14; proof p.A11

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelS_game
import Definitions.Def_ComplementarySourcing_IsEffortCandidate1
import Definitions.Def_ComplementarySourcing_IsEffortCandidate2
import Definitions.Def_ComplementarySourcing_candidateProfit1
import Definitions.Def_ComplementarySourcing_candidateProfit2
import Definitions.Def_ComplementarySourcing_smallestMaxIndex
import Definitions.Def_ComplementarySourcing_riskLevel

namespace ComplementarySourcing

/-- **Proposition 3** (Optimal Supplier Effort): if `rµ ≥ ϵ₁ + 2ϵ₀`, then
`(x^S_s, w^S) = (x_k, r − (ϵ_k − x_k)/(µ(1 + αx_k)²))`; and for realized `ϵ = ϵ_i` the manufacturer's optimal
effort is `0` if `x^S_s ≥ ϵ_i` and `min(µ(r − w^S)(1 + αx^S_s), (ϵ_i − x^S_s)/(1 + αx^S_s))` if `x^S_s ≤ ϵ_i`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Proposition 3, p.14 (PDF 14).

**Formalization Note.** Stated about `ModelS.game`, not obtained by substituting `w' = r − w`. The
`↔` carries existence and uniqueness of the optimal pair. -/
theorem proposition_3 {μ α r ε₀ σ x₁ x₂ π₁ π₂ xk wk wS : ℝ} {k : Fin 2} {s : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ) (hσ : σ ≤ ε₀)
    (hx₁ : IsEffortCandidate1 α ε₀ σ x₁) (hx₂ : IsEffortCandidate2 α ε₀ σ x₂)
    (hπ₁ : π₁ = candidateProfit1 μ α r ε₀ σ x₁) (hπ₂ : π₂ = candidateProfit2 μ α r ε₀ σ x₂)
    (hk : k = smallestMaxIndex π₁ π₂) (hxk : xk = ![x₁, x₂] k)
    (hwk : wk = wholesaleCandidate μ α (riskLevel ε₀ σ k) xk)
    (hwS : wS = r - wk) (hr : r * μ ≥ (ε₀ + σ) + 2 * ε₀)
    (hs : (ModelS.game μ α r ε₀ σ).IsFollowerStrategy s) :
    (∀ xs w, (ModelS.game μ α r ε₀ σ).IsEquilibrium s (xs, w) ↔ xs = xk ∧ w = wS) ∧
      ∀ i : Fin 2,
        (xk ≥ riskLevel ε₀ σ i → s (xk, wS) (riskLevel ε₀ σ i) = 0) ∧
        (xk ≤ riskLevel ε₀ σ i → s (xk, wS) (riskLevel ε₀ σ i) =
          min (μ * (r - wS) * (1 + α * xk)) ((riskLevel ε₀ σ i - xk) / (1 + α * xk))) := by sorry

end ComplementarySourcing
