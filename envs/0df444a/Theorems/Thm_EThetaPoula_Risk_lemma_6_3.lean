-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_6_3
-- name    : EThetaPoula.Risk.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:22.205144+00:00
-- url     : https://prove2.me/theorems/2a016a90-5c14-4cf4-b109-eb89c91162b0
-- title:
--   Lemma 6.3, p.23 — the Lyapunov drift condition
-- statement:
--   Under Assumptions 1–4, for every $\theta\in\mathbb R^d$ and $\bar p\in[2,\infty)\cap\mathbb N$, the Lyapunov function $V_{\bar p}(\theta):=(1+|\theta|^2)^{\bar p/2}$ satisfies
--   $$
--   -\langle\nabla V_{\bar p}(\theta),h(\theta)\rangle+\Delta V_{\bar p}(\theta)/\beta\le-c_{V,1}(\bar p)V_{\bar p}(\theta)+c_{V,2}(\bar p),
--   $$
--   where $c_{V,1}(\bar p):=a_h\bar p/4$, $c_{V,2}(\bar p):=(3/4)a_h\bar p\,v_{\bar p}(M_V(\bar p))$ and $M_V(\bar p):=(1/3+4b_h/(3a_h)+4d/(3a_h\beta)+4(\bar p-2)/(3a_h\beta))^{1/2}$.
--
--   This is the geometric drift condition for the generator of the Langevin SDE, which gives its stability and enters the constants of its contraction.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - encoding: no $\epsilon$ in these constants → $\epsilon$ is a free argument of `Model.params`; reason: the constants read here do not involve it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma 6.3, p.23

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma 6.3**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.23: under Assumptions 1–4,
the Lyapunov function `V_p̄`, `p̄ ∈ [2, ∞) ∩ ℕ`, satisfies the drift condition
`−⟨∇V_p̄(θ), h(θ)⟩ + ΔV_p̄(θ)/β ≤ −c_{V,1}(p̄) V_p̄(θ) + c_{V,2}(p̄)`.

**Formalization Note.** `ΔV_p̄` is Mathlib's Laplacian; `V_p̄` is smooth. The constants do not involve
`ϵ`. -/
theorem lemma_6_3 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (θ : Eucl d) (p : ℕ) (hp : 2 ≤ p) :
    let K := S.params C β ϵ
    (-inner ℝ (gradient (lyapunov p) θ) (S.h θ)
        + Laplacian.laplacian (lyapunov p) θ / β ≤
      -K.cV1 p * lyapunov p θ + K.cV2 p) := by sorry

end EThetaPoula.Risk
