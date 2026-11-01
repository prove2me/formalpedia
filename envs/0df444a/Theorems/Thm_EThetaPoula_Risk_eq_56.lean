-- Prove2me | Theorems.Thm_EThetaPoula_Risk_eq_56
-- name    : EThetaPoula.Risk.eq_56
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:24.379611+00:00
-- url     : https://prove2.me/theorems/1097dde4-f972-41a9-b404-d7ee874a9531
-- title:
--   (56), p.26 — $W_2$ between $\bar\zeta^{\lambda,n}$ and $Z^\lambda$
-- statement:
--   Under Assumptions 1–4, for $0<\lambda\le\lambda_{\max}$, $n\in\mathbb N_0$, $t\in(nT,(n+1)T]$, and every $\epsilon$ satisfying (48),
--   $$
--   W_2(\mathcal L(\bar\zeta^{\lambda,n}_t),\mathcal L(Z^\lambda_t))\le\lambda^{1/4}\bigl(e^{-\min\{\dot c,a_F\kappa^\sharp_2,a_h\}n/8}\bar C_4(E[V_{4(2r+1)}(\theta_0)])^{1/2}+\bar C_5\bigr),
--   $$
--   with $\bar C_4,\bar C_5$ of (57).
--
--   This is the second term of the splitting (55). It uses the contraction in $w_{1,2}$ and $W_2\le\sqrt{2w_{1,2}}$, which is why the rate drops to $\lambda^{1/4}$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - encoding: "$\epsilon>0$ is chosen such that" (48) holds → every $\epsilon$ satisfying (48), as a hypothesis, with the constants functions of $\epsilon$; reason: covers any choice the paper makes
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, (56), (57), p.26

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_wasserstein
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsInterpolation
import Definitions.Def_EThetaPoula_Risk_IsAuxiliaryProcess
import Definitions.Def_EThetaPoula_Risk_IsLangevinSolution
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Display (56)**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.26: under Assumptions 1–4,
for `0 < λ ≤ λ_max`, `n ∈ ℕ₀` and `t ∈ (nT, (n+1)T]`,
`W₂(L(ζ̄^{λ,n}_t), L(Z^λ_t)) ≤ λ^{1/4}(e^{−min{ċ, a_Fκ♯₂, a_h} n/8} C̄₄ (E[V_{4(2r+1)}(θ₀)])^{1/2} + C̄₅)`,
for every `ϵ` of (48), with `C̄₄`, `C̄₅` of (57). -/
theorem eq_56 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (hϵ : (S.params C β ϵ).EpsAdmissible) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B) (lam : ℝ) (hlam : 0 < lam)
    (hlamMax : lam ≤ (S.params C β ϵ).lamMax)
    (θb : ℝ≥0 → Ω → Eucl d) (hθb : S.IsInterpolation B lam β ε θb)
    (n : ℕ) (zb : ℝ≥0 → Ω → Eucl d) (hzb : S.IsAuxiliaryProcess B lam β θb n zb)
    (Z : ℝ≥0 → Ω → Eucl d) (hZ : S.IsLangevinSolution B β S.θ₀ Z) (t : ℝ≥0)
    (ht : (n * blockLength lam : ℝ≥0) < t) (ht' : t ≤ (n + 1) * blockLength lam) :
    let K := S.params C β ϵ
    WassersteinDRO.StrongDuality.wasserstein 2 (S.P.map (zb t))
        (S.P.map (Z (Real.toNNReal (lam * t)))) ≤
      ENNReal.ofReal (lam ^ (1 / 4 : ℝ) * (Real.exp (-K.mMin * n / 8) * K.C4Bar
        * √(∫ ω, lyapunov (4 * (2 * S.r + 1)) (S.θ₀ ω) ∂S.P) + K.C5Bar)) := by sorry

end EThetaPoula.Risk
