-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_6_6
-- name    : EThetaPoula.Risk.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:39.288815+00:00
-- url     : https://prove2.me/theorems/65b12d3d-c694-44b1-9b48-46f2023800d7
-- title:
--   Lemma 6.6, p.25 — $W_2$ between $\bar\theta^\lambda$ and $\bar\zeta^{\lambda,n}$
-- statement:
--   Under Assumptions 1–4, for $0<\lambda\le\lambda_{\max}$, $n\in\mathbb N_0$, $t\in(nT,(n+1)T]$,
--   $$
--   W_2(\mathcal L(\bar\theta^\lambda_t),\mathcal L(\bar\zeta^{\lambda,n}_t))\le\sqrt\lambda\bigl(e^{-na_F\kappa^\sharp_2/2}\bar C_0E[V_{4(2r+1)}(\theta_0)]+\bar C_1\bigr)^{1/2},
--   $$
--   with $\bar C_0,\bar C_1$ of (136).
--
--   This is the first term of the splitting (55). The step-size restriction and the bounds on $H-H_\lambda$ enter here, and this is where the discontinuity of $G$ is handled through its Lipschitz condition in average.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: no $\epsilon$ in these constants → $\epsilon$ is a free argument of `Model.params`; reason: the constants read here do not involve it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma 6.6, p.25; (136), p.42

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_wasserstein
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsInterpolation
import Definitions.Def_EThetaPoula_Risk_IsAuxiliaryProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma 6.6**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.25: under Assumptions 1–4,
for `0 < λ ≤ λ_max`, `n ∈ ℕ₀` and `t ∈ (nT, (n+1)T]`,
`W₂(L(θ̄^λ_t), L(ζ̄^{λ,n}_t)) ≤ √λ (e^{−n a_F κ♯₂/2} C̄₀ E[V_{4(2r+1)}(θ₀)] + C̄₁)^{1/2}`.

**Formalization Note.** `C̄₀`, `C̄₁` do not involve `ϵ`. -/
theorem lemma_6_6 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B) (lam : ℝ) (hlam : 0 < lam)
    (hlamMax : lam ≤ (S.params C β ϵ).lamMax)
    (θb : ℝ≥0 → Ω → Eucl d) (hθb : S.IsInterpolation B lam β ε θb)
    (n : ℕ) (zb : ℝ≥0 → Ω → Eucl d) (hzb : S.IsAuxiliaryProcess B lam β θb n zb) (t : ℝ≥0)
    (ht : (n * blockLength lam : ℝ≥0) < t) (ht' : t ≤ (n + 1) * blockLength lam) :
    let K := S.params C β ϵ
    WassersteinDRO.StrongDuality.wasserstein 2 (S.P.map (θb t)) (S.P.map (zb t)) ≤
      ENNReal.ofReal (√lam * √(Real.exp (-n * K.aF * K.kappaSharp / 2) * K.C0Bar
        * (∫ ω, lyapunov (4 * (2 * S.r + 1)) (S.θ₀ ω) ∂S.P) + K.C1Bar)) := by sorry

end EThetaPoula.Risk
