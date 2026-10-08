-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_lemma1_supergradient_ratio
-- name    : DataDrivenNV.WMS.lemma1_supergradient_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:26:36.556058+00:00
-- url     : https://prove2.me/theorems/63e29919-6b93-4a16-a7bc-54aa3491fc40
-- title:
--   Lemma 1, p. 14 — at the b/(b+h) quantile of a log-concave pdf, −(b+h)/h ≤ γ₁/γ₀ ≤ (b+h)/b
-- statement:
--   Let $b,h>0$ and let $f$ be a log-concave probability density on $\mathbb R$ with cdf $F$. Let $q^*=\inf\{q: F(q)\ge b/(b+h)\}$ be its $b/(b+h)$ quantile. Suppose $f(q^*)=\gamma_0>0$ and $\gamma_1\in\partial\log f(q^*)$, i.e. $\log f(x)\le\log f(q^*)+\gamma_1(x-q^*)$ whenever $f(x)>0$. Then
--   $$-\frac{b+h}{h}\ \le\ \frac{\gamma_1}{\gamma_0}\ \le\ \frac{b+h}{b}.$$
--
--   This gives the necessary condition on $(\gamma_0,\gamma_1)$ for the feasible set of the constrained problem (11) to be nonempty, and ensures that the endpoints of the extremal density (12) are well defined.
--
--   **Formalization Note** Log-concavity is `LogConcaveOn Set.univ f` in the power form; $\gamma_1\in\partial\log f(q^*)$ is the supergradient inequality on $\{f>0\}$ (the paper says "subgradient" of the concave $\log f$).
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 14, Lemma 1; proof EC.3, pp. ec8–ec9

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Lemma 1** (p. 14): if `f` is a log-concave pdf whose `b/(b+h)` quantile `q*` has
`f(q*) = γ₀ > 0` and `γ₁ ∈ ∂ log f(q*)`, then `−(b+h)/h ≤ γ₁/γ₀ ≤ (b+h)/b`. -/
theorem lemma1_supergradient_ratio (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (f : ℝ → ℝ) (hf : IsPdf f) (hlc : ConvexOptimization.LogConcaveOn Set.univ f)
    (γ₀ γ₁ : ℝ) (hγ₀ : 0 < γ₀) (hfq : f (quantileOf f (b / (b + h))) = γ₀)
    (hsg : IsLogSupergradient f (quantileOf f (b / (b + h))) γ₁) :
    -((b + h) / h) ≤ γ₁ / γ₀ ∧ γ₁ / γ₀ ≤ (b + h) / b := by sorry

end DataDrivenNV.WMS
