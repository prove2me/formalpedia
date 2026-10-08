-- Prove2me | Theorems.Thm_BoundedNV_Stakes_prop5_expected_profit_strict_mono
-- name    : BoundedNV.Stakes.prop5_expected_profit_strict_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:20.856752+00:00
-- url     : https://prove2.me/theorems/5807206b-1596-4a53-b980-3f49283ecc56
-- title:
--   Proposition 5, p. 580 — with the same β, utilities λ₁π and λ₂π with λ₁ > λ₂ give Eπ(X♭₁) > Eπ(X♭₂)
-- statement:
--   Let $S\subseteq\mathbb R$ be a measurable decision domain and $\pi:\mathbb R\to\mathbb R$ a measurable payoff. Two decision makers share the bounded-rationality parameter $\beta>0$ but face the utilities $u_1(x)=\lambda_1\pi(x)$ and $u_2(x)=\lambda_2\pi(x)$ with $\lambda_1>\lambda_2$. The behavioral decision $X^\flat_i$ has the logit density
--   $$\psi_i(x)=\frac{e^{\lambda_i\pi(x)/\beta}}{\int_S e^{\lambda_i\pi(v)/\beta}\,dv}\qquad(x\in S).$$
--   Assume that for $i=1,2$ both $e^{\lambda_i\pi/\beta}$ and $\pi\,e^{\lambda_i\pi/\beta}$ are integrable on $S$, and that $\pi$ is not almost everywhere constant on $S$. Then
--   $$E\pi(X^\flat_1)>E\pi(X^\flat_2).$$
--
--   A decision maker who holds a larger stake in the same payoff makes better decisions on average. In §7 this explains why giving a retailer a fixed share $\lambda<1$ of supply-chain profits fails to coordinate a boundedly rational chain, and why $\lambda>1$ may supercoordinate it.
--
--   **Formalization Note** The page leaves the following implicit. (1) $\beta>0$, the domain of eq. (2). (2) Measurability of $S$ and $\pi$, the standing convention. (3) Integrability of $e^{\lambda_i\pi/\beta}$ and $\pi e^{\lambda_i\pi/\beta}$ on $S$: without it Lean's integrals take the junk value $0$, so the logit law or the expected profit would not exist. (4) **Non-constancy of $\pi$ on $S$** is necessary: if $\pi$ is a.e. equal to a constant on $S$, both expectations equal that constant and the strict inequality fails; it also forces $S$ to have positive measure. Any real $\lambda_1>\lambda_2$ is allowed, including negative values and values above $1$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 580 (PDF p. 15), Proposition 5; proof p. 587 (PDF p. 22)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit

namespace BoundedNV.Stakes

open MeasureTheory

/-- Proposition 5, p. 580: two logit decision makers with the same bounded-rationality parameter
`β` and utilities `u₁ = λ₁ π`, `u₂ = λ₂ π` with `λ₁ > λ₂`; then `E π(X♭₁) > E π(X♭₂)`.
The integrability hypotheses make the logit laws and both expectations genuine; the
non-constancy of `π` on `S` is necessary (for constant `π` both sides are equal). -/
theorem prop5_expected_profit_strict_mono (S : Set ℝ) (hS : MeasurableSet S)
    (π : ℝ → ℝ) (hπ : Measurable π) (β lam₁ lam₂ : ℝ) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (hint₁ : IntegrableOn (fun x => Real.exp (lam₁ * π x / β)) S)
    (hint₂ : IntegrableOn (fun x => Real.exp (lam₂ * π x / β)) S)
    (hmom₁ : IntegrableOn (fun x => π x * Real.exp (lam₁ * π x / β)) S)
    (hmom₂ : IntegrableOn (fun x => π x * Real.exp (lam₂ * π x / β)) S)
    (hnc : ¬ ∃ k : ℝ, ∀ᵐ x ∂(volume.restrict S), π x = k) :
    BoundedNV.Uniform.logitExp S (fun x => lam₂ * π x) β π < BoundedNV.Uniform.logitExp S (fun x => lam₁ * π x) β π := by sorry

end BoundedNV.Stakes
