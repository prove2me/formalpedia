-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_6_9
-- name    : EThetaPoula.Risk.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:28.312242+00:00
-- url     : https://prove2.me/theorems/289f2808-878d-4bc2-93da-e0d51bda78ee
-- title:
--   Lemma 6.9, p.27 — $E[u(Z_\infty)]-u^*\le C_9/\beta$ and $C_9(\beta)/\beta\to0$
-- statement:
--   Under Assumptions 1–4, for $\beta>0$ with $\int e^{-\beta u}<\infty$,
--   $$
--   E[u(Z_\infty)]-u^*\le\frac{C_9}{\beta},\qquad C_9\equiv C_9(\beta):=\frac d2\log\Bigl(\frac{L_h(1+4\max\{\sqrt{b_h/a_h},\sqrt{2d/(\beta L_h)}\})^{2r}e}{a_h}\Bigl(\frac{\beta b_h}{d}+1\Bigr)\Bigr)+\log2,
--   $$
--   where $u^*:=\inf_\theta u(\theta)$, and $\lim_{\beta\to\infty}C_9(\beta)/\beta=0$.
--
--   This is the second term of the splitting (61), the concentration of the Gibbs measure near the minimizers. The limit is what makes the excess risk arbitrarily small.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - generalization: $\int e^{-\beta u}<\infty$ assumed for any $\beta>0$ → $\int e^{-\beta u}<\infty$ required for the fixed $\beta$ of the statement only; reason: a weaker hypothesis; the printed one implies it
--   - encoding: the expectation is written without an integrability claim → integrability of the integrand is a conclusion; reason: a Bochner integral of a non-integrable function is $0$, so the claim must carry it
--   - encoding: "for any $0<\lambda\le\lambda_{\max}$, $n\in\mathbb N_0$" → these quantifiers are omitted; reason: the statement mentions neither $\lambda$ nor $n$
--   - encoding: no $\epsilon$ in these constants → $\epsilon$ is a free argument of `Model.params`; reason: the constants read here do not involve it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma 6.9, (63), p.27

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open Filter Topology
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma 6.9**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.27: under Assumptions 1–4,
for `β > 0`, `E[u(Z_∞)] − u* ≤ C₉/β` with `C₉ ≡ C₉(β)` of (63), `u* := inf_θ u(θ)`, and
`lim_{β→∞} C₉(β)/β = 0`.

**Formalization Note.** `E[u(Z_∞)]` is `∫ u dπ_β`. The statement of the lemma mentions neither `λ`
nor `n`, so these idle quantifiers are omitted. The limit runs over the argument of `C9Fn`, whose
inputs `L_h, a_h, b_h, d` do not involve `β`. `BddBelow` guards the real infimum. -/
theorem lemma_6_9 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (hgibbs : Integrable fun θ : Eucl d => Real.exp (-β * S.u θ)) (ϵ : ℝ) :
    let K := S.params C β ϵ
    BddBelow (Set.range S.u) ∧
    Integrable S.u (S.piBeta β) ∧
    ∫ θ, S.u θ ∂S.piBeta β - ⨅ θ, S.u θ ≤ K.C9 / β ∧
    Tendsto (fun b : ℝ => K.C9Fn b / b) atTop (𝓝 0) := by sorry

end EThetaPoula.Risk
