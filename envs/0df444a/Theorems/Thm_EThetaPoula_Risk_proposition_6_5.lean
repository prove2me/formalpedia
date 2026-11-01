-- Prove2me | Theorems.Thm_EThetaPoula_Risk_proposition_6_5
-- name    : EThetaPoula.Risk.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:41.903673+00:00
-- url     : https://prove2.me/theorems/9f969961-078d-4f12-b0fd-14e49cc986c2
-- title:
--   Proposition 6.5, pp.24–25 — contraction of the Langevin SDE in $w_{1,2}$
-- statement:
--   Let Assumptions 1–4 hold, let $\theta'_0\in L^2$ be independent of $\mathcal F_\infty:=\sigma(\cup_{t\ge0}\mathcal F_t)$, and let $Z,Z'$ solve (37) with $Z_0=\theta_0$, $Z'_0=\theta'_0$. Then, for every $\epsilon$ satisfying (48) and every $t\ge0$,
--   $$
--   w_{1,2}(\mathcal L(Z_t),\mathcal L(Z'_t))\le\hat c\,e^{-\dot ct}\,w_{1,2}(\mathcal L(\theta_0),\mathcal L(\theta'_0)),
--   $$
--   where $\dot c:=\min\{\bar\phi,c_{V,1}(2),4c_{V,2}(2)\epsilon c_{V,1}(2)\}/2$ and $\hat c:=2(1+\dot c_0)\exp(\beta L_R\dot c_0^2/8+2\dot c_0)/\epsilon$, with $\bar\phi$ of (47).
--
--   This exponential contraction in the non-convex setting is what makes the error bound uniform in time.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - encoding: "$\epsilon>0$ is chosen such that" (48) holds → every $\epsilon$ satisfying (48), as a hypothesis, with the constants functions of $\epsilon$; reason: covers any choice the paper makes
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Proposition 6.5, (45)–(49), pp.24–25

import Mathlib
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsLangevinSolution
import Definitions.Def_EThetaPoula_Risk_semimetric
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Proposition 6.5**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, pp.24–25: under
Assumptions 1–4, for `θ'₀ ∈ L²` independent of `F_∞ = σ(∪_t F_t)` and the solution `Z'` of (37) with
`Z'₀ := θ'₀`,
`w_{1,2}(L(Z_t), L(Z'_t)) ≤ ĉ e^{−ċt} w_{1,2}(L(θ₀), L(θ'₀))`, for every `ϵ` of (48), with `ċ`, `ĉ` of
(46)–(49).

**Formalization Note.** `Z` and `Z'` solve (37) with the same Brownian motion. `ϵ` is universally
quantified under (48), which covers any choice the paper makes. -/
theorem proposition_6_5 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (hϵ : (S.params C β ϵ).EpsAdmissible)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B)
    (θ'₀ : Ω → Eucl d) (hθ'₀ : MemLp θ'₀ 2 S.P) (hind : IndepFun θ'₀ (fun ω t => B t ω) S.P)
    (Z Z' : ℝ≥0 → Ω → Eucl d) (hZ : S.IsLangevinSolution B β S.θ₀ Z)
    (hZ' : S.IsLangevinSolution B β θ'₀ Z') (t : ℝ≥0) :
    let K := S.params C β ϵ
    semimetric 2 (S.P.map (Z t)) (S.P.map (Z' t)) ≤
      ENNReal.ofReal (K.cHat * Real.exp (-K.cDot * t)) *
        semimetric 2 (S.P.map S.θ₀) (S.P.map θ'₀) := by sorry

end EThetaPoula.Risk
