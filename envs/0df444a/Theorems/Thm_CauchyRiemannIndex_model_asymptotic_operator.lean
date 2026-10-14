-- Prove2me | Theorems.Thm_CauchyRiemannIndex_model_asymptotic_operator
-- name    : CauchyRiemannIndex.model_asymptotic_operator
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:04:09.68564+00:00
-- url     : https://prove2.me/theorems/84880815-644d-441e-82d6-7b63a5eb5d6d
-- title:
--   Model asymptotic operators with prescribed Conley–Zehnder index
-- statement:
--   Let $k\in\mathbb{Z}$ and $\sigma>0$. On loops $\eta:S^1\to\mathbb{C}$ the asymptotic operator
--   $$\eta\mapsto-J_0\dot\eta-\pi k\,\eta-\sigma e^{2\pi ikt}\,\bar\eta$$
--   is nondegenerate and its Conley–Zehnder index is $k$.
--
--   **Formalization Note** This is $-J_0\partial_t-S(t)$ with $S(t)=\pi k\,\mathrm{Id}+\sigma\cdot$ `antilinearMat (exp (2πikt))`, where `antilinearMat β` is the symmetric real matrix of $z\mapsto\beta\bar z$ on $\mathbb{C}=\mathbb{R}^2$ (`Mat 1`).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Lemma 5.29, p. 103

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lemma 5.29 (p. 103): for `k ∈ ℤ` and `σ > 0`, the asymptotic operator
`η ↦ -J₀ ∂ₜη - π k η - σ e^{2πikt} η̄` on `C^∞(S¹, ℂ)` is nondegenerate and has Conley–Zehnder
index `k`. -/
theorem model_asymptotic_operator (k : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    IsNondegenerate (fun t : ℝ => (Real.pi * k) • (1 : Mat 1) +
        σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I))) ∧
      asymptoticCZIndex (fun t : ℝ => (Real.pi * k) • (1 : Mat 1) +
        σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I))) = k := by
  sorry

end CauchyRiemannIndex
