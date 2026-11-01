-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_6_4
-- name    : EThetaPoula.Risk.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:48.300296+00:00
-- url     : https://prove2.me/theorems/0c0e136f-583e-400e-b5cf-ce1a44f695ad
-- title:
--   Lemma 6.4, p.24 — moments of the auxiliary process
-- statement:
--   Let Assumptions 1–4 hold and $T=\lfloor1/\lambda\rfloor$.
--
--   1. For $0<\lambda\le\lambda_{1,\max}$, $n\in\mathbb N_0$, $t\ge nT$,
--   $$
--   E[V_2(\bar\zeta^{\lambda,n}_t)]\le e^{-\min\{a_h/2,a_F\kappa\}\lambda t}E[V_2(\theta_0)]+\mathring c_0+1+3v_2(M_V(2)).
--   $$
--   2. For $0<\lambda\le\lambda_{2,\max}$, $n\in\mathbb N_0$, $t\ge nT$,
--   $$
--   E[V_4(\bar\zeta^{\lambda,n}_t)]\le2e^{-\min\{a_h,a_F\kappa^\sharp_2\}\lambda t}E[V_4(\theta_0)]+2\mathring c_2+2+3v_4(M_V(4)).
--   $$
--
--   These are the bounds that the comparison of $\bar\zeta^{\lambda,n}$ with $Z^\lambda$ needs, uniformly in $n$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: the expectation is written without an integrability claim → integrability of the integrand is a conclusion; reason: a Bochner integral of a non-integrable function is $0$, so the claim must carry it
--   - encoding: no $\epsilon$ in these constants → $\epsilon$ is a free argument of `Model.params`; reason: the constants read here do not involve it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma 6.4, p.24

import Mathlib
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsInterpolation
import Definitions.Def_EThetaPoula_Risk_IsAuxiliaryProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma 6.4**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.24: under Assumptions 1–4,
the second and the fourth moment estimate of the auxiliary process `ζ̄^{λ,n}` of (43), for
`t ≥ nT`, `T = ⌊1/λ⌋`.

**Formalization Note.** Integrability of `V₂(ζ̄^{λ,n}_t)` and `V₄(ζ̄^{λ,n}_t)` is part of the conclusion,
since a Bochner integral of a non-integrable function is `0`. The constants do not involve `ϵ`. -/
theorem lemma_6_4 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B) :
    let K := S.params C β ϵ
    (∀ (lam : ℝ), 0 < lam → lam ≤ K.lamMaxP 1 → ∀ θb : ℝ≥0 → Ω → Eucl d,
      S.IsInterpolation B lam β ε θb → ∀ (n : ℕ) (zb : ℝ≥0 → Ω → Eucl d),
      S.IsAuxiliaryProcess B lam β θb n zb → ∀ t : ℝ≥0, (n * blockLength lam : ℝ≥0) ≤ t →
        Integrable (fun ω => lyapunov 2 (zb t ω)) S.P ∧
        ∫ ω, lyapunov 2 (zb t ω) ∂S.P ≤
          Real.exp (-min (K.ah / 2) (K.aF * K.kappa) * lam * t)
              * ∫ ω, lyapunov 2 (S.θ₀ ω) ∂S.P
            + K.c0ring + 1 + 3 * vFun 2 (K.MV 2)) ∧
    (∀ (lam : ℝ), 0 < lam → lam ≤ K.lamMaxP 2 → ∀ θb : ℝ≥0 → Ω → Eucl d,
      S.IsInterpolation B lam β ε θb → ∀ (n : ℕ) (zb : ℝ≥0 → Ω → Eucl d),
      S.IsAuxiliaryProcess B lam β θb n zb → ∀ t : ℝ≥0, (n * blockLength lam : ℝ≥0) ≤ t →
        Integrable (fun ω => lyapunov 4 (zb t ω)) S.P ∧
        ∫ ω, lyapunov 4 (zb t ω) ∂S.P ≤
          2 * Real.exp (-min K.ah (K.aF * K.kappaSharp) * lam * t)
              * ∫ ω, lyapunov 4 (S.θ₀ ω) ∂S.P
            + 2 * K.cRing 2 + 2 + 3 * vFun 4 (K.MV 4)) := by sorry

end EThetaPoula.Risk
