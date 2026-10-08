-- Prove2me | Theorems.Thm_BoundedNV_Stakes_eq54_55_single_crossing
-- name    : BoundedNV.Stakes.eq54_55_single_crossing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:16.079979+00:00
-- url     : https://prove2.me/theorems/1b487ece-08d8-4f52-a146-01dfc84a8482
-- title:
--   Proof of Proposition 5, eqs. (54)–(55), p. 587 — ψ₁(x) > ψ₂(x) iff π(x) > β ln K/(λ₁ − λ₂)
-- statement:
--   Let $S\subseteq\mathbb R$ have positive Lebesgue measure, let $\pi$ be a real function, $\beta>0$ and $\lambda_1>\lambda_2$. For $i=1,2$ let $u_i=\lambda_i\pi$, assume $e^{u_i/\beta}$ is integrable on $S$, and let
--   $$\psi_i(x)=\frac{e^{u_i(x)/\beta}}{\int_S e^{u_i(v)/\beta}\,dv}$$
--   be the logit density of $u_i$ on $S$. Put $K=\int_S e^{u_1(v)/\beta}dv\big/\int_S e^{u_2(v)/\beta}dv$. Then for every $x\in S$,
--   $$\psi_1(x)>\psi_2(x)\iff e^{(u_1(x)-u_2(x))/\beta}>K\iff \pi(x)>\frac{\beta\ln K}{\lambda_1-\lambda_2}.$$
--
--   This single-crossing property says the decision maker with the larger stake puts more weight exactly on the decisions whose payoff exceeds one threshold; it drives the stochastic dominance (56)–(57) and hence Proposition 5.
--
--   **Formalization Note** $\beta>0$, positive measure of $S$ and integrability of $e^{u_i/\beta}$ on $S$ are implicit on the page; they make both normalisers finite and positive, so $K>0$ and $\ln K$ is genuine.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 587 (PDF p. 22), proof of Proposition 5, eqs. (54)–(55)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit

namespace BoundedNV.Stakes

open MeasureTheory

/-- Proof of Proposition 5, eqs. (54)–(55), p. 587: with `K` the ratio of the normalizers of the
logit densities `ψᵢ` of the utilities `uᵢ = λᵢ π` (`λ₁ > λ₂`, same `β`), for every `x ∈ S`,
`ψ₁(x) > ψ₂(x) ⇔ e^{(u₁(x) − u₂(x))/β} > K ⇔ π(x) > β ln K / (λ₁ − λ₂)`. -/
theorem eq54_55_single_crossing (S : Set ℝ) (hSpos : 0 < volume S)
    (π : ℝ → ℝ) (β lam₁ lam₂ : ℝ) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (hint₁ : IntegrableOn (fun x => Real.exp (lam₁ * π x / β)) S)
    (hint₂ : IntegrableOn (fun x => Real.exp (lam₂ * π x / β)) S)
    (x : ℝ) (hx : x ∈ S) :
    let K := (∫ v in S, Real.exp (lam₁ * π v / β)) / (∫ v in S, Real.exp (lam₂ * π v / β))
    (BoundedNV.Uniform.logitDensity S (fun y => lam₂ * π y) β x < BoundedNV.Uniform.logitDensity S (fun y => lam₁ * π y) β x ↔
        K < Real.exp ((lam₁ * π x - lam₂ * π x) / β)) ∧
      (K < Real.exp ((lam₁ * π x - lam₂ * π x) / β) ↔
        β * Real.log K / (lam₁ - lam₂) < π x) := by sorry

end BoundedNV.Stakes
