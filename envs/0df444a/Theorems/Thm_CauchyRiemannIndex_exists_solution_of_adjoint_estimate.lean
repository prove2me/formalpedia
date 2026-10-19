-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_solution_of_adjoint_estimate
-- name    : CauchyRiemannIndex.exists_solution_of_adjoint_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:00:18.707884+00:00
-- url     : https://prove2.me/theorems/9de4a5e6-9448-4ca5-802f-914aa163d277
-- title:
--   Solvability with an $L^2$ bound from an estimate for the formal adjoint
-- statement:
--   Let $S^\pm$ be continuous loops of symmetric $2n\times2n$ matrices and let $S:\mathbb R\times S^1\to\mathbb R^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$. Let $B:\mathbb R\times\mathbb R\to\mathbb R^{2n\times2n}$ be continuous with $|B(x)v|\le M|v|$ for all $x,v$. Write $D=\partial_s+J_0\partial_t+S+B$ and
--   $$D^*\varphi=-\partial_s\varphi+J_0\partial_t\varphi+(S+B)^{T}\varphi$$
--   for its formal adjoint. Suppose that for some $C\ge0$
--   $$\|\varphi\|_{L^2}^2\le C\,\|D^*\varphi\|_{L^2}^2\qquad\text{for every test section }\varphi .$$
--   Then for every $f\in L^2(\mathbb R\times S^1,\mathbb R^{2n})$ there is $w\in W^{1,2}$ with $Dw=f$ and $\|w\|_{L^2}\le\sqrt C\,\|f\|_{L^2}$.
--
--   This turns an a priori estimate for the adjoint into surjectivity of $D:W^{1,2}\to L^2$ with a bounded solution operator into $L^2$; $B$ need not be asymptotic to anything.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and integrals over $\mathbb R\times S^1$ are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$); $\partial_s,\partial_t$ are `partialS`, `partialT`, and matrices act through `Matrix.toEuclideanLin`. $W^{1,2}$ is `W1p 2 n` (triples $(u,\partial_su,\partial_tu)$), $Dw$ is `crApply (fun x => S x + B x) w`, and the conclusion bounds the $L^2$ norm of the first component `w.1`. The bound on $B$ is stated for the operator `Matrix.toEuclideanLin (B x)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, proof of Proposition 5.24, p. 100 (p = 2)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `D_S` be asymptotic to loops `S±` of symmetric matrices and let `B` be a continuous
bounded matrix-valued function on the cylinder. If the formal adjoint
`φ ↦ -∂ₛφ + J₀ ∂ₜφ + (S + B)ᵀ φ` of `D_{S+B}` satisfies `‖φ‖₂² ≤ C ‖D_{S+B}^* φ‖₂²` for every
test section `φ`, then for every `f ∈ L²` there is `w ∈ W^{1,2}` with `D_{S+B} w = f` and
`‖w‖₂ ≤ √C ‖f‖₂`. -/
theorem exists_solution_of_adjoint_estimate (n : ℕ) (Splus Sminus : ℝ → Mat n)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus)
    (B : ℝ × ℝ → Mat n) (hBc : Continuous B)
    (hBb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (B x) v‖ ≤ M * ‖v‖)
    (C : ℝ) (hC : 0 ≤ C)
    (hest : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤
        C * ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x + B x)ᵀ (φ x)‖ ^ 2 ∂cylMeasure)
    (f : LpCyl n 2) :
    ∃ w ∈ W1p 2 n, crApply (fun x => S x + B x) w =ᵐ[cylMeasure] (f : ℝ × ℝ → Vec n) ∧
      ‖w.1‖ ≤ Real.sqrt C * ‖f‖ := by
  sorry

end CauchyRiemannIndex
