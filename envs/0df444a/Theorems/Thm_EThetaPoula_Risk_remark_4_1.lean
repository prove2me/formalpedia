-- Prove2me | Theorems.Thm_EThetaPoula_Risk_remark_4_1
-- name    : EThetaPoula.Risk.remark_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:35.910825+00:00
-- url     : https://prove2.me/theorems/f7b7bffd-da72-473d-949d-44150f2220f0
-- title:
--   Remark 4.1, p.16 — growth of $H$ and local Lipschitz bound for $h$
-- statement:
--   Under Assumptions 1, 2 and 3, for all $\theta,\bar\theta\in\mathbb R^d$, $x\in\mathbb R^m$,
--   $$
--   |H(\theta,x)|\le K_H(1+|x|)^\rho(1+|\theta|^{2r+1}),\qquad|h(\theta)-h(\bar\theta)|\le L_h(1+|\theta|+|\bar\theta|)^{2r}|\theta-\bar\theta|,
--   $$
--   where $K_H:=2^{2r}K_G+3\sqrt{2d}\,K_F$ and $L_h:=\max\{L_G+L_FE[(1+2|X_0|)^{\rho-1}],1\}$.
--
--   These are the growth and regularity facts used throughout the analysis. The stochastic gradient grows like $|\theta|^{2r+1}$, so the untamed Euler scheme is not stable.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - encoding: no $\beta$, $\epsilon$ in these constants → $\beta$, $\epsilon$ are free arguments of `Model.params`; reason: the constants read here do not involve them
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Remark 4.1, p.16

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Remark 4.1**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.16: under Assumptions 1, 2,
3, `|H(θ, x)| ≤ K_H (1 + |x|)^ρ (1 + |θ|^{2r+1})` and
`|h(θ) − h(θ̄)| ≤ L_h (1 + |θ| + |θ̄|)^{2r} |θ − θ̄|`.

**Formalization Note.** `K_H` and `L_h` do not involve `β` or `ϵ`, which are free arguments of
`Model.params` only. -/
theorem remark_4_1 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (h1 : S.Assumption1) (h2 : S.Assumption2 C)
    (h3 : S.Assumption3 C) (β ϵ : ℝ) :
    let K := S.params C β ϵ
    (∀ (θ : Eucl d) (x : Eucl m),
      ‖S.H θ x‖ ≤ K.KH * (1 + ‖x‖) ^ S.ρ * (1 + ‖θ‖ ^ (2 * S.r + 1))) ∧
    ∀ θ θ' : Eucl d,
      ‖S.h θ - S.h θ'‖ ≤ K.Lh * (1 + ‖θ‖ + ‖θ'‖) ^ (2 * S.r) * ‖θ - θ'‖ := by sorry

end EThetaPoula.Risk
