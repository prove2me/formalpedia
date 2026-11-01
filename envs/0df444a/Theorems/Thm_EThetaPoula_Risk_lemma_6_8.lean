-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_6_8
-- name    : EThetaPoula.Risk.lemma_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:35.137526+00:00
-- url     : https://prove2.me/theorems/d690418c-e72c-4592-84b4-13ef9056ac83
-- title:
--   Lemma 6.8, p.27 — $E[u(\theta^\lambda_n)]-E[u(Z_\infty)]$
-- statement:
--   Under Assumptions 1–4, for every $\beta>0$ with $\int e^{-\beta u}<\infty$ and every $\epsilon$ satisfying (48), for $0<\lambda\le\lambda_{\max}$ and $n\in\mathbb N_0$,
--   $$
--   E[u(\theta^\lambda_n)]-E[u(Z_\infty)]\le C_7e^{-C_6\lambda n}+C_8\lambda^{1/4},
--   $$
--   where $\mathcal L(Z_\infty)=\pi_\beta$ and $C_6,C_7,C_8$ are given by (62).
--
--   This is the first term of the splitting (61) of the excess risk. It turns the Wasserstein-2 estimate into a bound on the objective through the polynomial growth of $h$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: "$\epsilon>0$ is chosen such that" (48) holds → every $\epsilon$ satisfying (48), as a hypothesis, with the constants functions of $\epsilon$; reason: covers any choice the paper makes
--   - generalization: $\int e^{-\beta u}<\infty$ assumed for any $\beta>0$ → $\int e^{-\beta u}<\infty$ required for the fixed $\beta$ of the statement only; reason: a weaker hypothesis; the printed one implies it
--   - encoding: the expectation is written without an integrability claim → integrability of the integrand is a conclusion; reason: a Bochner integral of a non-integrable function is $0$, so the claim must carry it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma 6.8, (62), p.27

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma 6.8**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.27: under Assumptions 1–4, for
every `ϵ` of (48), `0 < λ ≤ λ_max` and `n ∈ ℕ₀`,
`E[u(θ^λ_n)] − E[u(Z_∞)] ≤ C₇ e^{−C₆λn} + C₈ λ^{1/4}`, with the constants of (62), where
`E[u(Z_∞)] = ∫ u dπ_β` because `L(Z_∞) = π_β`, (61).

**Formalization Note.** Integrability of `u(θ^λ_n)` and of `u` under `π_β` is part of the conclusion,
since a Bochner integral of a non-integrable function is `0`. -/
theorem lemma_6_8 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (hgibbs : Integrable fun θ : Eucl d => Real.exp (-β * S.u θ))
    (ϵ : ℝ) (hϵ : (S.params C β ϵ).EpsAdmissible) :
    let K := S.params C β ϵ
    Integrable S.u (S.piBeta β) ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ lam : ℝ, 0 < lam → lam ≤ K.lamMax → ∀ n : ℕ,
      Integrable (fun ω => S.u (S.theta lam β ε n ω)) S.P ∧
      ∫ ω, S.u (S.theta lam β ε n ω) ∂S.P - ∫ θ, S.u θ ∂S.piBeta β ≤
        K.C7 * Real.exp (-K.C6 * lam * n) + K.C8 * lam ^ (1 / 4 : ℝ) := by sorry

end EThetaPoula.Risk
