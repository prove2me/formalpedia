-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_A_2
-- name    : EThetaPoula.Risk.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:16.407712+00:00
-- url     : https://prove2.me/theorems/b30afcee-ab08-43a5-94bb-25acd40010a3
-- title:
--   Lemma A.2, p.40 — one-step fourth moment
-- statement:
--   Under Assumptions 1–4, for $0<\lambda\le\lambda_{\max}$ and $t\ge0$,
--   $$
--   E[|\bar\theta^\lambda_t-\bar\theta^\lambda_{\lfloor t\rfloor}|^4]\le\lambda^2\bigl(e^{-\lambda a_F\kappa^\sharp_2\lfloor t\rfloor}\bar C_{0,1}E[|\theta_0|^{4(2r+1)}]+\bar C_{1,1}\bigr),
--   $$
--   with $\bar C_{0,1},\bar C_{1,1}$ of (130).
--
--   This one-step bound is the source of the order $\lambda^{1/2}$ in the comparison of $\bar\theta^\lambda$ with $\bar\zeta^{\lambda,n}$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: the expectation is written without an integrability claim → integrability of the integrand is a conclusion; reason: a Bochner integral of a non-integrable function is $0$, so the claim must carry it
--   - encoding: no $\epsilon$ in these constants → $\epsilon$ is a free argument of `Model.params`; reason: the constants read here do not involve it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma A.2, (130), p.40

import Mathlib
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsInterpolation
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma A.2**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.40: under Assumptions 1–4,
for `0 < λ ≤ λ_max` and `t ≥ 0`, the one-step fourth moment bound
`E[|θ̄^λ_t − θ̄^λ_{⌊t⌋}|⁴] ≤ λ²(e^{−λ a_F κ♯₂ ⌊t⌋} C̄_{0,1} E[|θ₀|^{4(2r+1)}] + C̄_{1,1})`.

**Formalization Note.** Integrability of the left side is part of the conclusion. The constants do
not involve `ϵ`. -/
theorem lemma_A_2 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B) (lam : ℝ) (hlam : 0 < lam)
    (hlamMax : lam ≤ (S.params C β ϵ).lamMax)
    (θb : ℝ≥0 → Ω → Eucl d) (hθb : S.IsInterpolation B lam β ε θb) (t : ℝ≥0) :
    let K := S.params C β ϵ
    Integrable (fun ω => ‖θb t ω - θb (⌊t⌋₊ : ℝ≥0) ω‖ ^ 4) S.P ∧
    ∫ ω, ‖θb t ω - θb (⌊t⌋₊ : ℝ≥0) ω‖ ^ 4 ∂S.P ≤
      lam ^ 2 *
        (Real.exp (-lam * K.aF * K.kappaSharp * ⌊t⌋₊) * K.C01 * K.thetaMom + K.C11) := by sorry

end EThetaPoula.Risk
