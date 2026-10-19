-- Prove2me | Theorems.Thm_CauchyRiemannIndex_memLp_of_le_of_le
-- name    : CauchyRiemannIndex.memLp_of_le_of_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T11:22:01.769536+00:00
-- url     : https://prove2.me/theorems/b8cee81b-385f-49f3-8fdd-c91a5710eca9
-- title:
--   A function in $L^p\cap L^q$ lies in $L^r$ for every $p\le r\le q$
-- statement:
--   Let $(X,\mu)$ be a measure space, $E$ a normed group, and $0<p\le r\le q<\infty$. If $f:X\to E$ satisfies $f\in L^p(\mu)$ and $f\in L^q(\mu)$, then $f\in L^r(\mu)$:
--   $$L^p(\mu)\cap L^q(\mu)\;\subseteq\;L^r(\mu)\qquad(0<p\le r\le q<\infty).$$
--
--   This is the inclusion of $L^p\cap L^q$ in all intermediate Lebesgue spaces, on an arbitrary (possibly infinite) measure space. It is used to pass integrability between exponents, for example for functions known to lie in $L^p$ and in a higher $L^q$.
--
--   **Formalization Note.** Exponents are in `ℝ≥0∞`, with $p\neq0$ and $q\neq\infty$; membership is `MemLp f p μ`.
-- source:
--   Standard; e.g. G. B. Folland, Real Analysis: Modern Techniques and Their Applications, 2nd ed., Wiley 1999, Proposition 6.10

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- If `f ∈ Lᵖ ∩ L^q` with `0 < p ≤ r ≤ q < ∞`, then `f ∈ L^r`. -/
theorem memLp_of_le_of_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {p q r : ℝ≥0∞} (hp0 : p ≠ 0) (hpr : p ≤ r) (hrq : r ≤ q)
    (hqt : q ≠ ⊤) (hfp : MemLp f p μ) (hfq : MemLp f q μ) : MemLp f r μ := by
  sorry

end CauchyRiemannIndex
