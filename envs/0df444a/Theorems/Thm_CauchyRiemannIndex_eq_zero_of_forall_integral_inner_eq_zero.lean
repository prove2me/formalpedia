-- Prove2me | Theorems.Thm_CauchyRiemannIndex_eq_zero_of_forall_integral_inner_eq_zero
-- name    : CauchyRiemannIndex.eq_zero_of_forall_integral_inner_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T10:11:08.473002+00:00
-- url     : https://prove2.me/theorems/6d963e80-e5f3-41cf-95ac-cf3c9c19b6c0
-- title:
--   An $L^q$ function orthogonal to all of $L^p$ vanishes
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure, $E$ a complete real inner product space and $1\le p,q<\infty$. If $g\in L^q(\mu;E)$ satisfies
--   $$\int\langle f,g\rangle\,d\mu=0\qquad\text{for every }f\in L^p(\mu;E),$$
--   then $g=0$ in $L^q(\mu;E)$.
--
--   The pairing $(f,g)\mapsto\int\langle f,g\rangle\,d\mu$ therefore separates the points of $L^q$. This is the injectivity half of the duality between $L^p$ and $L^q$, and it is used to identify annihilators of subspaces of $L^p$ inside $L^q$.
--
--   **Formalization Note.** $L^p(\mu;E)$ is `Lp E p μ` with `Fact (1 ≤ p)` and `p ≠ ⊤`, and likewise for $q$. No relation between $p$ and $q$ is assumed; the integral is the Bochner integral of $x\mapsto\langle f(x),g(x)\rangle$, which is $0$ by convention when that function is not integrable.
-- source:
--   Standard; see e.g. H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Section 4.3

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- Let `μ` be σ-finite, `E` a complete real inner product space and `1 ≤ p, q < ∞`. If
`g ∈ L^q(μ; E)` satisfies `∫ ⟨f, g⟩ dμ = 0` for every `f ∈ L^p(μ; E)`, then `g = 0`. -/
theorem eq_zero_of_forall_integral_inner_eq_zero {α E : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (g : Lp E q μ) (hg : ∀ f : Lp E p μ, ∫ x, inner ℝ (f x) (g x) ∂μ = 0) : g = 0 := by
  sorry

end CauchyRiemannIndex
