-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_winding_of_antilinear
-- name    : CauchyRiemannIndex.asymptoticCZIndex_eq_winding_of_antilinear
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:50:38.564531+00:00
-- url     : https://prove2.me/theorems/687e922d-6199-4993-b6e3-fc048a7061fe
-- title:
--   The Conley–Zehnder index of an asymptotic operator with a nondegenerate antilinear deformation equals the winding number
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2\times2}$ be a continuous loop of symmetric matrices and $\beta:S^1\to\mathbb{C}\setminus\{0\}$ a continuous loop with winding number $w\in\mathbb{Z}$. Suppose that for every $\sigma\ge0$ the asymptotic operator
--   $$\eta\mapsto-J_0\dot\eta-S\eta-\sigma\beta\bar\eta$$
--   is nondegenerate. Then
--   $$\mu_{CZ}(-J_0\partial_t-S)=w.$$
--
--   This identifies the Conley–Zehnder index of an asymptotic operator that admits a nondegenerate antilinear deformation with the winding number of the deformation (Wendl, Lecture 5, §5.8).
--
--   **Formalization Note** Loops are continuous $1$-periodic maps on $\mathbb{R}$; $\eta\mapsto\beta\bar\eta$ is the real matrix `antilinearMat β`, so the deformed operator is the asymptotic operator of the loop $S+\sigma\cdot$`antilinearMat ∘ β`, and nondegeneracy is `IsNondegenerate` (applied with $\sigma=0$ it covers $S$ itself). The winding number is given by a continuous argument $\theta$: $\beta(t)=|\beta(t)|e^{i\theta(t)}$ with $\theta(1)-\theta(0)=2\pi w$. The index is `asymptoticCZIndex S`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103 (cylinder, trivial bundle)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lecture 5 (§ 5.8, pp. 102–103), trivial line bundle over `S¹`: let `S` be a loop of
symmetric `2 × 2` matrices and `β : S¹ → ℂ \ {0}` a continuous loop of winding number `w` such
that the asymptotic operator `η ↦ -J₀ η' - S η - σ β η̄` is nondegenerate for every `σ ≥ 0`.
Then `μ_CZ(-J₀ ∂ₜ - S) = w`. -/
theorem asymptoticCZIndex_eq_winding_of_antilinear (S : ℝ → Mat 1) (hS : IsSymLoop S)
    (β : ℝ → ℂ) (hβ : Continuous β) (hper : Function.Periodic β 1) (hnz : ∀ t, β t ≠ 0)
    (hnd : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S t + σ • antilinearMat (β t)))
    (w : ℤ) (θ : ℝ → ℝ) (hθ : Continuous θ)
    (harg : ∀ t, β t = ‖β t‖ * Complex.exp (θ t * Complex.I))
    (hw : θ 1 - θ 0 = 2 * Real.pi * w) :
    asymptoticCZIndex S = w := by
  sorry

end CauchyRiemannIndex
