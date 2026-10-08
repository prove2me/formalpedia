-- Prove2me | Theorems.Thm_BoundedNV_Stakes_eq56_57_stochastic_dominance
-- name    : BoundedNV.Stakes.eq56_57_stochastic_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:32.678621+00:00
-- url     : https://prove2.me/theorems/e695b215-4b5c-4844-ad51-48d33dd55041
-- title:
--   Proof of Proposition 5, eqs. (56)–(57), p. 587 — π(X♭₁) stochastically dominates π(X♭₂)
-- statement:
--   Let $S\subseteq\mathbb R$ be measurable with positive Lebesgue measure, $\pi$ a measurable real function, $\beta>0$ and $\lambda_1>\lambda_2$. For $i=1,2$ assume $e^{\lambda_i\pi/\beta}$ is integrable on $S$ and let $X^\flat_i$ have the logit density $\psi_i$ of the utility $u_i=\lambda_i\pi$ on $S$. Then for every real $k$,
--   $$P\big(\pi(X^\flat_1)\ge k\big)=\int_{\{v\in S:\ \pi(v)\ge k\}}\psi_1(v)\,dv\ \ge\ \int_{\{v\in S:\ \pi(v)\ge k\}}\psi_2(v)\,dv=P\big(\pi(X^\flat_2)\ge k\big),$$
--   that is, $\pi(X^\flat_1)$ first-order stochastically dominates $\pi(X^\flat_2)$.
--
--   A larger stake shifts the law of the realised payoff upward in the strongest stochastic order; the monotonicity of the expected payoff (Proposition 5) follows.
--
--   **Formalization Note** The paper prints (56)–(57) with a strict $>$. That is false for $k$ above the essential supremum of $\pi$ on $S$ (both probabilities are $0$) and for $k$ below its essential infimum (both are $1$); the proof's own conclusion is stochastic dominance, which is the weak inequality for every $k$, and that is stated here. (57) also integrates over $\{\pi\le k\}$ where the complement of $\{\pi\ge k\}$ is $\{\pi<k\}$; with the weak inequality this is immaterial. $\beta>0$, measurability, positive measure of $S$ and the integrability of $e^{\lambda_i\pi/\beta}$ are implicit on the page and make both densities genuine probability densities.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 587 (PDF p. 22), proof of Proposition 5, eqs. (56)–(57)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit

namespace BoundedNV.Stakes

open MeasureTheory

/-- Proof of Proposition 5, eqs. (56)–(57), p. 587: `π(X♭₁)` first-order stochastically dominates
`π(X♭₂)`, i.e. `P(π(X♭₂) ≥ k) ≤ P(π(X♭₁) ≥ k)` for every real `k`, where `X♭ᵢ` has the logit
density of the utility `uᵢ = λᵢ π` (`λ₁ > λ₂`, same `β`). The paper prints a strict `>`, which
fails for `k` outside the essential range of `π`; the weak dominance is what the proof concludes. -/
theorem eq56_57_stochastic_dominance (S : Set ℝ) (hS : MeasurableSet S) (hSpos : 0 < volume S)
    (π : ℝ → ℝ) (hπ : Measurable π) (β lam₁ lam₂ : ℝ) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (hint₁ : IntegrableOn (fun x => Real.exp (lam₁ * π x / β)) S)
    (hint₂ : IntegrableOn (fun x => Real.exp (lam₂ * π x / β)) S)
    (k : ℝ) :
    ∫ v in S ∩ {v | k ≤ π v}, BoundedNV.Uniform.logitDensity S (fun y => lam₂ * π y) β v ≤
      ∫ v in S ∩ {v | k ≤ π v}, BoundedNV.Uniform.logitDensity S (fun y => lam₁ * π y) β v := by sorry

end BoundedNV.Stakes
