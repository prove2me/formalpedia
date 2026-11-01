-- Prove2me | Theorems.Thm_EThetaPoula_Risk_corollary_4_5
-- name    : EThetaPoula.Risk.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:47.915909+00:00
-- url     : https://prove2.me/theorems/4f7c9006-acd3-4392-aff9-943a42fb75fe
-- title:
--   Corollary 4.5, p.18 — the Wasserstein-2 rate, with the explicit constants (60)
-- statement:
--   Under Assumptions 1–4, for every $\beta>0$ with $\int e^{-\beta u}<\infty$ and every $\epsilon$ satisfying (48), the constants $C_3,C_4,C_5$ of (60) are positive and, for all $0<\lambda\le\lambda_{\max}$ and $n\in\mathbb N_0$,
--   $$
--   W_2(\mathcal L(\theta^\lambda_n),\pi_\beta)\le C_4e^{-C_3\lambda n}(E[|\theta_0|^{4(2r+1)}]+1)^{1/2}+C_5\lambda^{1/4}.
--   $$
--
--   The bound is non-asymptotic and explicit, and it is the input for the expected excess risk.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: "$\epsilon>0$ is chosen such that" (48) holds → every $\epsilon$ satisfying (48), as a hypothesis, with the constants functions of $\epsilon$; reason: covers any choice the paper makes
--   - generalization: $\int e^{-\beta u}<\infty$ assumed for any $\beta>0$ → $\int e^{-\beta u}<\infty$ required for the fixed $\beta$ of the statement only; reason: a weaker hypothesis; the printed one implies it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Corollary 4.5, p.18; (60), p.26

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_wasserstein
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Corollary 4.5**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.18: under Assumptions 1–4,
for every `β > 0` and every `ϵ` of (48), the constants `C₃, C₄, C₅` of (60) are positive and, for
`0 < λ ≤ λ_max`, `n ∈ ℕ₀`,
`W₂(L(θ^λ_n), π_β) ≤ C₄ e^{−C₃λn}(E[|θ₀|^{4(2r+1)}] + 1)^{1/2} + C₅λ^{1/4}`.

**Formalization Note.** The constants are the explicit ones of (60), not existential. They do not
depend on `λ`, `n` or the `ε` of (7). -/
theorem corollary_4_5 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (hgibbs : Integrable fun θ : Eucl d => Real.exp (-β * S.u θ))
    (ϵ : ℝ) (hϵ : (S.params C β ϵ).EpsAdmissible) :
    let K := S.params C β ϵ
    0 < K.C3 ∧ 0 < K.C4 ∧ 0 < K.C5 ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ lam : ℝ, 0 < lam → lam ≤ K.lamMax → ∀ n : ℕ,
      WassersteinDRO.StrongDuality.wasserstein 2 (S.P.map (S.theta lam β ε n)) (S.piBeta β) ≤
        ENNReal.ofReal (K.C4 * Real.exp (-K.C3 * lam * n) * √(K.thetaMom + 1)
          + K.C5 * lam ^ (1 / 4 : ℝ)) := by sorry

end EThetaPoula.Risk
