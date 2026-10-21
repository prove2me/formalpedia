-- Prove2me | Theorems.Thm_CauchyRiemannIndex_index_eq_winding_of_antilinear_deformation
-- name    : CauchyRiemannIndex.index_eq_winding_of_antilinear_deformation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T21:05:16.505358+00:00
-- url     : https://prove2.me/theorems/8d41a842-5fa1-4ed4-b726-02aad90f553e
-- title:
--   The index of a Cauchy–Riemann operator on the cylinder from antilinear deformations of its asymptotic operators
-- statement:
--   Let $n=1$, let $S^\pm$ be continuous loops of symmetric $2\times2$ matrices with nondegenerate asymptotic operators, and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2\times2}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$. Suppose that for each sign there are a continuous loop $S'^\pm$ of symmetric matrices with
--   $$\mu_{CZ}(-J_0\partial_t-S'^\pm)=\mu_{CZ}(-J_0\partial_t-S^\pm)$$
--   and a continuous loop $\beta_\pm:S^1\to\mathbb{C}\setminus\{0\}$ such that the asymptotic operator
--   $$\eta\mapsto-J_0\dot\eta-S'^\pm\eta-\sigma\beta_\pm\bar\eta$$
--   is nondegenerate for every $\sigma\ge0$. Then the index of $D_S:W^{1,2}\to L^2$ is
--   $$\operatorname{ind}D_S=\operatorname{wind}(\beta_+)-\operatorname{wind}(\beta_-).$$
--
--   **Formalization Note** $\eta\mapsto\beta\bar\eta$ is the matrix `antilinearMat β`, so the deformed operator is the asymptotic operator of the loop $S'^\pm+\sigma\cdot$`antilinearMat ∘ β±`. The winding numbers $w_\pm$ are given through continuous arguments: $\beta_\pm(t)=|\beta_\pm(t)|e^{i\theta_\pm(t)}$ with $\theta_\pm(1)-\theta_\pm(0)=2\pi w_\pm$. The index is `crIndex 2 S`; for the cylinder $\chi=0$ and $c_1^\tau=0$ in Wendl's formula. The exponent is $p=2$ (Wendl, Assumption 5.7).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Lemma 5.28, p. 102 (cylinder, trivial line bundle, global trivialization, p = 2)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lemma 5.28 (p. 102), on the cylinder with the trivial line bundle and its global
trivialization, `p = 2`: let `D_S` (`n = 1`) be asymptotic to nondegenerate loops `S±` of symmetric
matrices. Suppose that for each end there are a loop `S'±` of symmetric matrices with
`μ_CZ(-J₀ ∂ₜ - S'±) = μ_CZ(-J₀ ∂ₜ - S±)` and a nowhere-vanishing loop `β± : S¹ → ℂ` such that
`η ↦ -J₀ η' - S'± η - σ β± η̄` is nondegenerate for every `σ ≥ 0`. Then
`ind D_S = wind(β⁺) - wind(β⁻)`. -/
theorem index_eq_winding_of_antilinear_deformation (Splus Sminus : ℝ → Mat 1)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (S'plus S'minus : ℝ → Mat 1) (h'plus : IsSymLoop S'plus) (h'minus : IsSymLoop S'minus)
    (hμplus : asymptoticCZIndex S'plus = asymptoticCZIndex Splus)
    (hμminus : asymptoticCZIndex S'minus = asymptoticCZIndex Sminus)
    (βplus βminus : ℝ → ℂ) (hβplus : Continuous βplus) (hβminus : Continuous βminus)
    (hperplus : Function.Periodic βplus 1) (hperminus : Function.Periodic βminus 1)
    (hnzplus : ∀ t, βplus t ≠ 0) (hnzminus : ∀ t, βminus t ≠ 0)
    (hndplus : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S'plus t + σ • antilinearMat (βplus t)))
    (hndminus : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S'minus t + σ • antilinearMat (βminus t)))
    (wplus wminus : ℤ) (θplus θminus : ℝ → ℝ) (hθplus : Continuous θplus)
    (hθminus : Continuous θminus)
    (hargplus : ∀ t, βplus t = ‖βplus t‖ * Complex.exp (θplus t * Complex.I))
    (hargminus : ∀ t, βminus t = ‖βminus t‖ * Complex.exp (θminus t * Complex.I))
    (hwplus : θplus 1 - θplus 0 = 2 * Real.pi * wplus)
    (hwminus : θminus 1 - θminus 0 = 2 * Real.pi * wminus) :
    crIndex 2 S = wplus - wminus := by
  sorry

end CauchyRiemannIndex
