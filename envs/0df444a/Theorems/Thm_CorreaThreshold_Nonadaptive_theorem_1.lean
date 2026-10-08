-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_theorem_1
-- name    : CorreaThreshold.Nonadaptive.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:13.507266+00:00
-- url     : https://prove2.me/theorems/5588aae2-5b91-452f-94f0-f3389bbc5349
-- title:
--   Theorem 1, p. 1459 — nonadaptive thresholds attain (1 − 1/e) E[max_i X_i]
-- statement:
--   Let $X_1,\ldots,X_n$ be independent nonnegative random variables, with $n\ge1$. There exist fixed thresholds $\tau_1,\ldots,\tau_n\in[0,\infty]$ such that, writing $Y_i=\mathbf1_{\{X_i>\tau_i\}}$,
--
--   $$\mathbb E\!\left[\frac{\sum_i X_iY_i}{\sum_iY_i}\right]\ge\left(1-\frac1e\right)\mathbb E\!\left[\max_i X_i\right],\qquad 0/0:=0.$$
--
--   Under uniformly random arrival, the left side is the expected prize of taking the first observation above its assigned threshold. The theorem gives the paper's guarantee for nonadaptive stopping.
--
--   **Formalization Note** Indices are 0-based. Nonnegativity is assumed almost surely, a distributionally equivalent version of the paper's nonnegative random variables. The thresholds are chosen before seeing the sample, may equal $\infty$, and use strict acceptance. Both expectations are extended nonnegative integrals, so heavy-tailed variables remain in scope. The statement covers atoms and makes no continuity assumption.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1459, Theorem 1 (first stated p. 1455); https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Setting

namespace CorreaThreshold.Nonadaptive

open MeasureTheory ProbabilityTheory

/-- Theorem 1: deterministic nonadaptive thresholds attain `1 - 1/e` of the prophet's reward. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P) :
    ∃ τ : Fin n → ENNReal,
      ENNReal.ofReal (1 - Real.exp (-1)) *
        (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (ratio τ X ω) ∂P) := by sorry

end CorreaThreshold.Nonadaptive
