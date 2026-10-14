-- Prove2me | Theorems.Thm_CauchyRiemannIndex_memW1p_of_weak_solution
-- name    : CauchyRiemannIndex.memW1p_of_weak_solution
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:00:55.018711+00:00
-- url     : https://prove2.me/theorems/9d70c664-74b5-483c-8be6-f66bb14ca463
-- title:
--   Global regularity of weak L^p solutions of Cauchy–Riemann equations on the cylinder
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. If $\eta\in L^p$ and $f\in L^p$ satisfy $D_S\eta=f$ weakly, that is,
--   $$\int_{\mathbb{R}\times S^1}\langle D_S^*\varphi,\eta\rangle=\int_{\mathbb{R}\times S^1}\langle\varphi,f\rangle\quad\text{for every test section }\varphi,\qquad D_S^*\varphi=-\partial_s\varphi+J_0\partial_t\varphi+S^{\mathsf T}\varphi,$$
--   then $\eta\in W^{1,p}$ and $D_S\eta=f$.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. The conclusion is `∃ w ∈ W1p p n, w.1 = η ∧ crApply S w =ᵐ f`: $\eta$ is the first component of an element of $W^{1,p}$ on which $D_S$ equals $f$ almost everywhere. Integrals are over the strip $\mathbb{R}\times[0,1)$; $D_S^*$ is the formal adjoint of $D_S$ for the real $L^2$ pairing.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Proposition 4.6, p. 70 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Proposition 4.6 (p. 70), case `k = 1`: let `D_S` be asymptotic to loops `S±` of
symmetric matrices and `1 < p < ∞`. If `η ∈ L^p` satisfies `D_S η = f` weakly for some
`f ∈ L^p`, i.e. `∫ ⟨D_S^* φ, η⟩ = ∫ ⟨φ, f⟩` for every test section `φ`, where
`D_S^* φ = -∂ₛφ + J₀ ∂ₜφ + S(s, t)ᵀ φ` is the formal adjoint, then `η ∈ W^{1,p}` and
`D_S η = f`. -/
theorem memW1p_of_weak_solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (η f : LpCyl n p)
    (hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (η x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure) :
    ∃ w ∈ W1p p n, w.1 = η ∧ crApply S w =ᵐ[cylMeasure] (f : ℝ × ℝ → Vec n) := by
  sorry

end CauchyRiemannIndex
