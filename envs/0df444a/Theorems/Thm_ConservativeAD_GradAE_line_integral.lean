-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_line_integral
-- name    : ConservativeAD.GradAE.line_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:50.260602+00:00
-- url     : https://prove2.me/theorems/675f1e77-57c5-4d5a-8d05-b3278905207b
-- title:
--   Proof of Theorem 1 — $f(x+tv)-f(x+sv)=\int_s^t\langle v,a(x+\tau v)\rangle d\tau$ for a measurable selection $a$
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field, $f$ a potential for $D$, and $a:\mathbb R^p\to\mathbb R^p$ a Borel measurable selection of $D$, i.e. $a(y)\in D(y)$ for every $y$. Then for every base point $x\in\mathbb R^p$, every direction $v\in\mathbb R^p$ and all real numbers $s<t$, the function $\tau\mapsto\langle v,a(x+\tau v)\rangle$ is Lebesgue integrable on $[s,t]$ and
--
--   $$
--   f(x+tv)-f(x+sv)=\int_s^t\langle v,a(x+\tau v)\rangle\,d\tau .
--   $$
--
--   This is the first step of the proof of Theorem 1: along every line, the potential is the integral of any measurable selection of the field. It holds for *every* selection, not only for a maximizing one.
--
--   **Formalization Note** The selection is a hypothesis; the existence of a measurable selection (Kuratowski–Ryll-Nardzewski, Aliprantis–Border Corollary 18.15) is not assumed or claimed. "Measurable" is Borel measurability.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 9, §3.1, proof of Theorem 1, display after 'elementary change of variable'

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- §3.1, proof of Theorem 1: for a potential `f` of `D` and a (Borel) measurable
selection `a` of `D`, along every line segment the function `τ ↦ ⟨v, a (x + τ v)⟩` is integrable
on `[s, t]` and `f (x + t v) - f (x + s v) = ∫_s^t ⟨v, a (x + τ v)⟩ dτ`. -/
theorem line_integral {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f)
    (a : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (ha : Measurable a)
    (haD : ∀ y, a y ∈ D y) :
    ∀ (x v : EuclideanSpace ℝ (Fin p)) (s t : ℝ), s < t →
      IntervalIntegrable (fun τ : ℝ => inner ℝ v (a (x + τ • v))) volume s t ∧
      f (x + t • v) - f (x + s • v) = ∫ τ in s..t, inner ℝ v (a (x + τ • v)) := by sorry

end ConservativeAD.GradAE
