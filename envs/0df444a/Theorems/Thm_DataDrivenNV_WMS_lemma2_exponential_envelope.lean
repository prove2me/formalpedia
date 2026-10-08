-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_lemma2_exponential_envelope
-- name    : DataDrivenNV.WMS.lemma2_exponential_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:30:38.181105+00:00
-- url     : https://prove2.me/theorems/049656a2-d938-4d65-9720-f34b658fdd5b
-- title:
--   Lemma 2, p. 15 — a log-concave pdf lies below its exponential envelope γ₀e^{γ₁(x−t)}
-- statement:
--   Let $f$ be a log-concave probability density on $\mathbb R$ and let $t$ be a point with $f(t)=\gamma_0>0$ (so $t$ is in the support of $f$). Suppose $\gamma_1\in\partial\log f(t)$, i.e. $\log f(x)\le\log f(t)+\gamma_1(x-t)$ whenever $f(x)>0$. Then for every $x\in\mathbb R$,
--   $$f(x)\ \le\ \gamma_0\,e^{\gamma_1(x-t)} .$$
--
--   Fixing a supergradient of $\log f$ bounds how fast the density can grow or decay; this envelope is what makes the truncated exponential (12) dominate every density of the class $\mathbb L_{q^*,\gamma_0,\gamma_1}$.
--
--   **Formalization Note** "$t$ in its support" is expressed by $f(t)=\gamma_0>0$. The bound is claimed at every $x$, including the points where $f(x)=0$.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 15, Lemma 2; proof EC.4, p. ec9

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Lemma 2** (p. 15): if `f` is a log-concave pdf, `f(t) = γ₀ > 0` and `γ₁ ∈ ∂ log f(t)`, then
`f(x) ≤ γ₀ e^{γ₁ (x − t)}` for every `x`. -/
theorem lemma2_exponential_envelope (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f)
    (t γ₀ γ₁ : ℝ) (hγ₀ : 0 < γ₀) (hft : f t = γ₀) (hsg : IsLogSupergradient f t γ₁) :
    ∀ x, f x ≤ γ₀ * Real.exp (γ₁ * (x - t)) := by sorry

end DataDrivenNV.WMS
