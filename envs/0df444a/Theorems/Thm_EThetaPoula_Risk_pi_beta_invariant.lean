-- Prove2me | Theorems.Thm_EThetaPoula_Risk_pi_beta_invariant
-- name    : EThetaPoula.Risk.pi_beta_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:44.907358+00:00
-- url     : https://prove2.me/theorems/f6ca22bb-e52c-48c2-899c-c133fe18ee30
-- title:
--   §6.2, p.25 and (58), p.26 — $\pi_\beta$ is invariant for (38), and $W_2$ bound
-- statement:
--   Let Assumptions 1–4 hold, $\beta>0$, $\int e^{-\beta u}<\infty$, and let $\epsilon$ satisfy (48). Let $B$ be a standard Brownian motion independent of the data.
--
--   1. $\pi_\beta$ is the invariant measure of (38): if $Z_0$ has law $\pi_\beta$, is independent of $B$, and $Z$ solves (37) from $Z_0$, then $\mathcal L(Z^\lambda_t)=\pi_\beta$ for all $\lambda>0$, $t\ge0$.
--   2. If $Z$ solves (37) from $\theta_0$, then
--   $$
--   W_2(\mathcal L(Z^\lambda_t),\pi_\beta)\le\sqrt2\,w_{1,2}^{1/2}(\mathcal L(Z^\lambda_t),\pi_\beta)\le\sqrt{2\hat c}\,e^{-\dot c\lambda t/2}\,w_{1,2}^{1/2}(\mathcal L(\theta_0),\pi_\beta).
--   $$
--
--   The bound (58) is the third term of the splitting (55) of the Wasserstein-2 distance.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - encoding: "$\epsilon>0$ is chosen such that" (48) holds → every $\epsilon$ satisfying (48), as a hypothesis, with the constants functions of $\epsilon$; reason: covers any choice the paper makes
--   - generalization: $\int e^{-\beta u}<\infty$ assumed for any $\beta>0$ → $\int e^{-\beta u}<\infty$ required for the fixed $\beta$ of the statement only; reason: a weaker hypothesis; the printed one implies it
--   - generalization: (58) is used for $0<\lambda\le\lambda_{\max}$, $t\in(nT,(n+1)T]$ → every $\lambda>0$, $t\ge0$; reason: this contains the range the paper uses
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.2, p.25; (58), p.26

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_wasserstein
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsLangevinSolution
import Definitions.Def_EThetaPoula_Risk_semimetric
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **`π_β` is invariant, and (58)**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.2, p.25 and
p.26: under Assumptions 1–4, `π_β` is the invariant measure of (38), and
`W₂(L(Z^λ_t), π_β) ≤ √2 w_{1,2}^{1/2}(L(Z^λ_t), π_β) ≤ √(2ĉ) e^{−ċλt/2} w_{1,2}^{1/2}(L(θ₀), π_β)`,
for every `ϵ` of (48).

**Formalization Note.** `Z^λ_t` is `Z_{λt}`, so invariance of (38) is stated at time `λt`, for a solution
started from law `π_β` independently of `B`. The paper uses (58) for `0 < λ ≤ λ_max`; it holds for every
`λ > 0`, `t ≥ 0`. -/
theorem pi_beta_invariant {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (hgibbs : Integrable fun θ : Eucl d => Real.exp (-β * S.u θ))
    (ϵ : ℝ) (hϵ : (S.params C β ϵ).EpsAdmissible)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B) :
    let K := S.params C β ϵ
    (∀ (Z0 : Ω → Eucl d), Measurable Z0 → S.P.map Z0 = S.piBeta β →
      IndepFun Z0 (fun ω t => B t ω) S.P → ∀ Z : ℝ≥0 → Ω → Eucl d,
      S.IsLangevinSolution B β Z0 Z → ∀ (lam : ℝ), 0 < lam → ∀ t : ℝ≥0,
        S.P.map (Z (Real.toNNReal (lam * t))) = S.piBeta β) ∧
    (∀ Z : ℝ≥0 → Ω → Eucl d, S.IsLangevinSolution B β S.θ₀ Z →
      ∀ (lam : ℝ), 0 < lam → ∀ t : ℝ≥0,
        WassersteinDRO.StrongDuality.wasserstein 2 (S.P.map (Z (Real.toNNReal (lam * t))))
            (S.piBeta β) ≤
          ENNReal.ofReal √2 *
            semimetric 2 (S.P.map (Z (Real.toNNReal (lam * t)))) (S.piBeta β) ^ (1 / 2 : ℝ) ∧
        ENNReal.ofReal √2 *
            semimetric 2 (S.P.map (Z (Real.toNNReal (lam * t)))) (S.piBeta β) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (√(2 * K.cHat) * Real.exp (-K.cDot * lam * t / 2)) *
            semimetric 2 (S.P.map S.θ₀) (S.piBeta β) ^ (1 / 2 : ℝ)) := by sorry

end EThetaPoula.Risk
