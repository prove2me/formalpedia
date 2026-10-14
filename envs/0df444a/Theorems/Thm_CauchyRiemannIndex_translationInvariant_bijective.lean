-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_bijective
-- name    : CauchyRiemannIndex.translationInvariant_bijective
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:00:35.242801+00:00
-- url     : https://prove2.me/theorems/58e43b4d-dbfd-4919-a125-4c0244819d19
-- title:
--   Translation-invariant Cauchy–Riemann operators with nondegenerate asymptotics are isomorphisms
-- statement:
--   Let $1<p<\infty$ and let $S_\infty$ be a continuous loop of symmetric matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. Then
--   $$\partial_s+J_0\partial_t+S_\infty(t):W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2n})\to L^p(\mathbb{R}\times S^1,\mathbb{R}^{2n})$$
--   is an isomorphism.
--
--   **Formalization Note** The operator is $D_S$ with $S(s,t)=S_\infty(t)$. The conclusion is `crKernel p S = ⊥ ∧ crRange p S = ⊤`, i.e. bijectivity, which for a bounded operator between Banach spaces is the same as being an isomorphism. $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$, $p\ne\infty$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 4.11 (p. 71), case `k = 1`: for `1 < p < ∞` and a nondegenerate loop `S∞`
of symmetric matrices, the translation-invariant operator
`∂ₛ + J₀ ∂ₜ + S∞(t) : W^{1,p}(ℝ × S¹, ℝ²ⁿ) → L^p(ℝ × S¹, ℝ²ⁿ)` is an isomorphism: it is
injective and onto. -/
theorem translationInvariant_bijective (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    crKernel p (fun x : ℝ × ℝ => Sinf x.2) = ⊥ ∧ crRange p (fun x : ℝ × ℝ => Sinf x.2) = ⊤ := by
  sorry

end CauchyRiemannIndex
