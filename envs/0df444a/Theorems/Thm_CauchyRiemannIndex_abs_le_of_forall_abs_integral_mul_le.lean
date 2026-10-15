-- Prove2me | Theorems.Thm_CauchyRiemannIndex_abs_le_of_forall_abs_integral_mul_le
-- name    : CauchyRiemannIndex.abs_le_of_forall_abs_integral_mul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T20:35:58.081358+00:00
-- url     : https://prove2.me/theorems/4f4e9518-16a2-46b6-837b-100370062c67
-- title:
--   A function on $[0,1)$ whose pairings with periodic continuous functions are $L^1$-bounded is essentially bounded
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be integrable on $[0,1)$ and let $K\in\mathbb R$. Suppose that
--   $$\Big|\int_0^1\varphi(t)\,h(t)\,dt\Big|\le K\int_0^1|\varphi(t)|\,dt$$
--   for every continuous $1$-periodic function $\varphi:\mathbb R\to\mathbb R$. Then
--   $$|h(t)|\le K\qquad\text{for almost every }t\in[0,1).$$
--
--   This is the elementary half of the duality $L^1(S^1)^*=L^\infty(S^1)$, phrased with continuous periodic test functions: an $L^1$-bounded linear functional given by an integrable density has an essentially bounded density with the same bound. It converts weak $L^1\to L^\infty$ estimates for periodic problems into pointwise almost-everywhere bounds.
--
--   **Formalization Note.** Integrals over $[0,1)$ are Lebesgue integrals over `Set.Ico 0 1`; the conclusion is an almost-everywhere statement for Lebesgue measure restricted to `Set.Ico 0 1`. No sign condition on $K$ is assumed.
-- source:
--   Standard L^1-L^infinity duality on the circle; see e.g. W. Rudin, Real and Complex Analysis, 3rd ed., Theorem 6.16

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Group.Integral

namespace CauchyRiemannIndex

open MeasureTheory

/-- Let `h : ℝ → ℝ` be integrable on `[0, 1)` and `K : ℝ`. If
`|∫₀¹ φ h| ≤ K ∫₀¹ |φ|` for every continuous `1`-periodic `φ : ℝ → ℝ`, then `|h t| ≤ K`
for almost every `t ∈ [0, 1)`. -/
theorem abs_le_of_forall_abs_integral_mul_le (h : ℝ → ℝ) (K : ℝ)
    (hh : IntegrableOn h (Set.Ico 0 1))
    (hK : ∀ φ : ℝ → ℝ, Continuous φ → Function.Periodic φ 1 →
      |∫ t in Set.Ico (0 : ℝ) 1, φ t * h t| ≤ K * ∫ t in Set.Ico (0 : ℝ) 1, |φ t|) :
    ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)), |h t| ≤ K := by
  sorry

end CauchyRiemannIndex
