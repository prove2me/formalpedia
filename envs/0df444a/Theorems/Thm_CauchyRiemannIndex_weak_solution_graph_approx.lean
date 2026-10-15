-- Prove2me | Theorems.Thm_CauchyRiemannIndex_weak_solution_graph_approx
-- name    : CauchyRiemannIndex.weak_solution_graph_approx
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T09:40:16.119347+00:00
-- url     : https://prove2.me/theorems/e3b3f8f6-e78f-42e6-8cdf-373a77998038
-- title:
--   Weak $L^p$ solutions of $\partial_s\eta+J_0\partial_t\eta=f$ on the cylinder are graph-norm limits of test sections
-- statement:
--   Let $1\le p<\infty$, let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ on $\mathbb R^{2n}$, and consider the cylinder $\mathbb R\times S^1$, $S^1=\mathbb R/\mathbb Z$, with coordinates $(s,t)$. A test section is a smooth map $\varphi:\mathbb R\times\mathbb R\to\mathbb R^{2n}$ that is $1$-periodic in $t$ and vanishes for $|s|$ large. Let $\eta,f\in L^p(\mathbb R\times S^1,\mathbb R^{2n})$ satisfy $\partial_s\eta+J_0\partial_t\eta=f$ weakly, that is,
--   $$\int_{\mathbb R\times S^1}\big\langle-\partial_s\varphi+J_0\partial_t\varphi,\ \eta\big\rangle=\int_{\mathbb R\times S^1}\langle\varphi,f\rangle\qquad\text{for every test section }\varphi.$$
--   Then for every $\varepsilon>0$ there is a test section $u$ with
--   $$\|u-\eta\|_{L^p}\le\varepsilon\qquad\text{and}\qquad\|\partial_su+J_0\partial_tu-f\|_{L^p}\le\varepsilon.$$
--
--   So the weak extension of the constant-coefficient Cauchy–Riemann operator $\partial_s+J_0\partial_t$ on $L^p$ coincides with the closure of its restriction to test sections. It is used for the $W^{1,p}$ regularity of weak $L^p$ solutions of Cauchy–Riemann type equations on the cylinder (Wendl, Proposition 4.6).
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `Vec n` $=$ `EuclideanSpace ℝ (Fin n ⊕ Fin n)` and $J_0$ is `J₀ n`, acting through `Matrix.toEuclideanLin`. Integrals over the cylinder are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`), and $L^p$ is `LpCyl n p` with $p$ in `ℝ≥0∞`, `Fact (1 ≤ p)` and $p\ne\infty$. Test sections are `IsTestSection`; $\partial_s,\partial_t$ are `partialS`, `partialT`. The operator $\partial_su+J_0\partial_tu$ is written `crOp (fun _ => 0) u`, and $\|\cdot\|_{L^p}$ is `eLpNorm` with values in $[0,\infty]$, as is $\varepsilon$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Proposition 4.6, p. 70 (setting of the weak Cauchy-Riemann equation on the cylinder)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Weak `L^p` solutions of `∂ₛη + J₀ ∂ₜη = f` on the cylinder are graph-norm limits of test
sections: if `η, f ∈ L^p` (`1 ≤ p < ∞`) and `∫ ⟨-∂ₛφ + J₀ ∂ₜφ, η⟩ = ∫ ⟨φ, f⟩` for every test
section `φ`, then for every `ε > 0` there is a test section `u` with `‖u - η‖_p ≤ ε` and
`‖∂ₛu + J₀ ∂ₜu - f‖_p ≤ ε`. -/
theorem weak_solution_graph_approx (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    (η f : LpCyl n p)
    (hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x)) (η x)
          ∂cylMeasure = ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (u - ⇑η) p cylMeasure ≤ ε ∧
      eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - ⇑f) p cylMeasure ≤ ε := by
  sorry

end CauchyRiemannIndex
