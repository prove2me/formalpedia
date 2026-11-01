-- Prove2me | Theorems.Thm_EThetaPoula_Risk_remark_4_2
-- name    : EThetaPoula.Risk.remark_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:24.854838+00:00
-- url     : https://prove2.me/theorems/a10e8a0c-e8bd-4141-9d7e-d752f40c6047
-- title:
--   Remark 4.2, p.17 — dissipativity (32), (33), existence of a minimizer, one-sided Lipschitz bound (34)
-- statement:
--   Under Assumptions 1–4, for all $\theta,\bar\theta\in\mathbb R^d$:
--
--   1. $\langle\theta,E[F(\theta,X_0)]\rangle\ge a_F|\theta|^{2r+2}-b_F$, (32);
--   2. $\langle\theta,h(\theta)\rangle\ge a_h|\theta|^2-b_h$, (33);
--   3. $u$ has a minimum $\theta^*\in\mathbb R^d$;
--   4. $L_R>0$ and $\langle\theta-\bar\theta,h(\theta)-h(\bar\theta)\rangle\ge-L_R|\theta-\bar\theta|^2$, (34).
--
--   Here $a_F,b_F,a_h,b_h,L_R$ are the explicit constants of the remark. Clause 3 is what makes $u^*:=\inf u$ a real number in the main theorem, and (33), (34) drive the contraction of the Langevin SDE.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - encoding: no $\beta$, $\epsilon$ in these constants → $\beta$, $\epsilon$ are free arguments of `Model.params`; reason: the constants read here do not involve them
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Remark 4.2, (32)–(34), p.17

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Remark 4.2**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.17: under Assumptions 1–4,
the dissipativity (32) of `F`, the dissipativity (33) of `h`, the existence of a minimizer `θ*` of
`u`, and the one-sided Lipschitz bound (34) with `L_R > 0`.

**Formalization Note.** The constants do not involve `β` or `ϵ`, which are free arguments of
`Model.params` only. -/
theorem remark_4_2 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β ϵ : ℝ) :
    let K := S.params C β ϵ
    (∀ θ : Eucl d, K.aF * ‖θ‖ ^ (2 * S.r + 2) - K.bF ≤
      inner ℝ θ (∫ ω, S.F θ (S.X 0 ω) ∂S.P)) ∧
    (∀ θ : Eucl d, K.ah * ‖θ‖ ^ 2 - K.bh ≤ inner ℝ θ (S.h θ)) ∧
    (∃ θs : Eucl d, ∀ θ, S.u θs ≤ S.u θ) ∧
    0 < K.LR ∧
    ∀ θ θ' : Eucl d, -K.LR * ‖θ - θ'‖ ^ 2 ≤ inner ℝ (θ - θ') (S.h θ - S.h θ') := by sorry

end EThetaPoula.Risk
