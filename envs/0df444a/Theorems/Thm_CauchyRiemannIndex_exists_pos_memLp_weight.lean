-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_pos_memLp_weight
-- name    : CauchyRiemannIndex.exists_pos_memLp_weight
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T23:21:01.89789+00:00
-- url     : https://prove2.me/theorems/8ab3a1cc-32d2-4246-9163-78375bc13e61
-- title:
--   A $\sigma$-finite measure has an everywhere positive measurable function in $L^p$, $0<p<\infty$
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure on $\alpha$ and $0<p<\infty$. Then there is a measurable $w:\alpha\to\mathbb R$ with
--   $$w(x)>0\ \text{ for every } x\in\alpha,\qquad w\in L^p(\mu).$$
--
--   Such a weight turns a $\sigma$-finite measure into the finite measure $|w|^p\mu$ with the same null sets. It is used to reduce statements about $\sigma$-finite measures to finite ones.
--
--   **Formalization Note.** $p\in$ `ℝ≥0∞` with $p\ne0$, $p\ne\infty$; the conclusion is `∃ w : α → ℝ, (∀ x, 0 < w x) ∧ Measurable w ∧ MemLp w p μ`.
-- source:
--   G. B. Folland, Real Analysis, 2nd ed., Wiley 1999, Exercise 2.14 / proof of Theorem 6.15, p. 191

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace CauchyRiemannIndex

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- A σ-finite measure admits an everywhere positive measurable weight in `L^p`, `0 < p < ∞`. -/
theorem exists_pos_memLp_weight {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    ∃ w : α → ℝ, (∀ x, 0 < w x) ∧ Measurable w ∧ MemLp w p μ := by
  sorry

end CauchyRiemannIndex
