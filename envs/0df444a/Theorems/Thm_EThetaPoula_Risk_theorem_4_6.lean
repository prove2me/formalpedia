-- Prove2me | Theorems.Thm_EThetaPoula_Risk_theorem_4_6
-- name    : EThetaPoula.Risk.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:32.432717+00:00
-- url     : https://prove2.me/theorems/ed642825-f9ad-4caf-97b2-1477b78fb2ef
-- title:
--   Theorem 4.6, p.18 — $E[u(\theta^\lambda_n)]-u^*\le C_7e^{-C_6\lambda n}+C_8\lambda^{1/4}+C_9/\beta$ with the explicit constants (62)–(63)
-- statement:
--   Let Assumptions 1–4 hold. For every $\beta>0$ with $\int e^{-\beta u}<\infty$ and every $\epsilon$ satisfying (48): $u$ is bounded below, the constants $C_6,C_7,C_8$ of (62) and $C_9$ of (63) are positive, and for every $0<\varepsilon<1$, $0<\lambda\le\lambda_{\max}$ of (36) and $n\in\mathbb N_0$, $u(\theta^\lambda_n)$ is integrable and
--   $$
--   E[u(\theta^\lambda_n)]-u^*\le C_7e^{-C_6\lambda n}+C_8\lambda^{1/4}+\frac{C_9}{\beta},\qquad u^*:=\inf_{\theta\in\mathbb R^d}u(\theta).
--   $$
--
--   This is the main optimization guarantee: the iterates of e-TH$\varepsilon$O POULA, run with a discontinuous stochastic gradient, approximately minimize $u$, and because $C_9(\beta)/\beta\to0$ the excess risk can be made arbitrarily small by choosing $\beta$, then $\lambda$, then $n$.
--
--   **Formalization Note** The constants are the explicit tower of `Params`, not existential ones; for fixed $\beta$ an existential $C_9$ could absorb the whole limit. They do not depend on $\lambda$, $n$ or $\varepsilon$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: "$\epsilon>0$ is chosen such that" (48) holds → every $\epsilon$ satisfying (48), as a hypothesis, with the constants functions of $\epsilon$; reason: covers any choice the paper makes
--   - generalization: $\int e^{-\beta u}<\infty$ assumed for any $\beta>0$ → $\int e^{-\beta u}<\infty$ required for the fixed $\beta$ of the statement only; reason: a weaker hypothesis; the printed one implies it
--   - encoding: the expectation is written without an integrability claim → integrability of the integrand is a conclusion; reason: a Bochner integral of a non-integrable function is $0$, so the claim must carry it
--   - encoding: $u^*:=\inf u$, finite by the minimum of Remark 4.2 → `BddBelow` is a conclusion; reason: a real infimum of an unbounded family is $0$
--   - encoding: "there exist constants $C_6,\dots,C_9>0$ … given explicitly in (62), (63)" → the explicit constants, with their positivity as a conclusion; reason: the explicit constants are the content of the theorem
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Theorem 4.6, p.18; (62), (63), p.27

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Theorem 4.6**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.18: under Assumptions 1–4,
for every `β > 0`, `u` is bounded below, the constants `C₆, C₇, C₈` of (62) and `C₉` of (63) are
positive, and, for every `0 < λ ≤ λ_max` of (36) and `n ∈ ℕ₀`,
`E[u(θ^λ_n)] − u* ≤ C₇ e^{−C₆λn} + C₈ λ^{1/4} + C₉/β`, with `u* := inf_θ u(θ)`.

**Formalization Note.** The constants are the explicit tower of `Params`, not existential: an
existential `C₉` for fixed `β` would absorb the whole limit. `ϵ` is universally quantified under (48),
which covers any choice the paper makes; `C₆, C₇, C₈` depend on it. The constants do not depend on
`λ`, `n` or the `ε ∈ (0, 1)` of (7). Integrability of `u(θ^λ_n)` is part of the conclusion, since a
Bochner integral of a non-integrable function is `0`, and `BddBelow` keeps `⨅` from being a junk
value. `∫ e^{−βu} < ∞` is required for this `β` only. -/
theorem theorem_4_6 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (hgibbs : Integrable fun θ : Eucl d => Real.exp (-β * S.u θ))
    (ϵ : ℝ) (hϵ : (S.params C β ϵ).EpsAdmissible) :
    let K := S.params C β ϵ
    BddBelow (Set.range S.u) ∧
    0 < K.C6 ∧ 0 < K.C7 ∧ 0 < K.C8 ∧ 0 < K.C9 ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ lam : ℝ, 0 < lam → lam ≤ K.lamMax → ∀ n : ℕ,
      Integrable (fun ω => S.u (S.theta lam β ε n ω)) S.P ∧
      ∫ ω, S.u (S.theta lam β ε n ω) ∂S.P - ⨅ θ, S.u θ ≤
        K.C7 * Real.exp (-K.C6 * lam * n) + K.C8 * lam ^ (1 / 4 : ℝ) + K.C9 / β := by sorry

end EThetaPoula.Risk
