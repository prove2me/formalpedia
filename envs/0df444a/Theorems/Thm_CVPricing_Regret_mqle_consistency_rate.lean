-- Prove2me | Theorems.Thm_CVPricing_Regret_mqle_consistency_rate
-- name    : CVPricing.Regret.mqle_consistency_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:38:12.572418+00:00
-- url     : https://prove2.me/theorems/b38e082a-50d8-4b5b-b2b9-85dd690b06a4
-- title:
--   Proposition 3 — under CVP with α > 1/2 the MQLE exists eventually, is strongly consistent, and E[‖â_t − a⁽⁰⁾‖² 1_{t>T_ρ₀}] = O(log t / t^α)
-- statement:
--   Consider the demand model with prices set by Controlled Variance Pricing with $\alpha > 1/2$ and deterministic initial prices $p_1 \ne p_2$, and assume (3) has at most one root. Then:
--
--   1. almost surely, a solution $\hat a_t$ of (3) exists for all sufficiently large $t$;
--   2. $\hat a_t \to a^{(0)}$ almost surely;
--   3. there is $\rho_0 > 0$ such that, with $T_{\rho_0}$ the random time (9), $\mathbb E[T_{\rho_0}^{1/2}] < \infty$ and
--
--   $$\mathbb E\big[\|\hat a_t - a^{(0)}\|^2\, \mathbf 1_{t > T_{\rho_0}}\big] = O\Big(\frac{\log t}{t^\alpha}\Big), \tag{10}$$
--
--   that is, there is $K > 0$ with $\mathbb E[\|\hat a_t - a^{(0)}\|^2 \mathbf 1_{t > T_{\rho_0}}] \le K \log t / t^\alpha$ for every $t \ge 2$.
--
--   This is the learning half of the regret analysis: the exploration enforced by CVP is enough for the quasi-likelihood estimates to converge at the stated rate.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm. $T_{\rho_0}$ takes values in $\mathbb N \cup \{\infty\}$ and $\mathbb E[T_{\rho_0}^{1/2}]$ is a lower Lebesgue integral in $[0,\infty]$. The rate is stated for $t \ge 2$, since the estimate needs two distinct prices and $\log 1 = 0$. The integrand of (10) is also asserted to be integrable, so the expectation is a genuine one. Uniqueness of the root of (3) and determinism of $p_1, p_2$ are disclosed hypotheses; part 2 is stated for every root, which under uniqueness is the MQLE.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 776 (PDF 8), Proposition 3, eqs. (9)–(10)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process

open MeasureTheory KeskinZeevi.SufficientConditions
open scoped ENNReal

namespace CVPricing.Regret

/-- Proposition 3 (den Boer–Zwart 2014, p. 776): under CVP with `α > 1/2`, a solution `â_t` of (3)
eventually exists and `â_t → a⁽⁰⁾` almost surely; moreover there is `ρ₀ > 0` with
`E[T_{ρ₀}^{1/2}] < ∞` and `E[‖â_t − a⁽⁰⁾‖² 1_{t > T_{ρ₀}}] = O(log t / t^α)` (eq. (10)), stated for
`t ≥ 2` with an explicit constant `K`. Initial prices are deterministic; the MQLE is assumed unique
(disclosed). The integrand of (10) is also asserted integrable, so the expectation is genuine. -/
theorem mqle_consistency_rate (M : Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    (∀ᵐ ω ∂P, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a) ∧
    (∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ a,
        IsMQLE M (fun s => p s ω) (fun s => d s ω) t a → euclidNorm (a - M.a0) < ε) ∧
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      (∫⁻ ω, ((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ∂P) < ⊤ ∧
      ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
        Integrable (fun ω => if (t : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) P ∧
        ∫ ω, (if (t : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) ∂P
          ≤ K * (Real.log t / (t : ℝ) ^ α) := by sorry

end CVPricing.Regret
