-- Prove2me | Theorems.Thm_DixmierMalliavin_exists_eq_integral_mul_comp_mul_exp_smul_add
-- name    : DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/0151385d-ae42-567d-915f-28372df6304c
-- title:
--   One-parameter Dixmier–Malliavin factorisation along exp(tX)
-- statement:
--   Let $A$ be a normed ring that is also a normed algebra over $\mathbb{R}$ and is complete as a metric space, let $X \in A$, let $\varepsilon$ be a real number with $0 < \varepsilon$, and let $\Phi : A \to \mathbb{C}$ be a function which is $C^\infty$ in the real sense and has compact support. The assertion is that there exist a function $\Phi_1 : A \to \mathbb{C}$ and functions $\varphi, \psi : \mathbb{R} \to \mathbb{C}$ such that: $\Phi_1$ is $C^\infty$ and its topological support (the closure of the set where it is nonzero) is contained in that of $\Phi$; $\varphi$ and $\psi$ are $C^\infty$ with topological supports contained in the closed interval $[-\varepsilon, \varepsilon]$; and for every $x \in A$,
--   $$\Phi(x) = \int_{\mathbb{R}} \varphi(t)\,\Phi_1\big(x \cdot \exp(t \cdot X)\big)\,dt \;+\; \int_{\mathbb{R}} \psi(t)\,\Phi\big(x \cdot \exp(t \cdot X)\big)\,dt,$$
--   the integrals being Bochner integrals against Lebesgue measure on $\mathbb{R}$ and $\exp$ denoting the exponential of the normed algebra $A$, applied to the scalar multiple $t \cdot X$. No smallness or nondegeneracy condition on $X$ is imposed, and $\Phi_1$ is produced abstractly rather than by an explicit formula.
--
--   This is the one-parameter (single direction $X$) step of the Dixmier–Malliavin factorisation, expressing a smooth compactly supported function as a sum of two convolutions along the one-parameter subgroup $t \mapsto \exp(tX)$ with factors supported arbitrarily near $0$. It is obtained from the approximation statement [`DixmierMalliavin.exists_contDiff_tendsto_integral_mul`](thm.html#DixmierMalliavin.exists_contDiff_tendsto_integral_mul), and is used in turn by [`DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul`](thm.html#DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul), the finitely many directions version.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DixmierMalliavin_exists_eq_integral_mul_comp_mul_exp_smul_add.lean

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (X : A) (ε : ℝ) (hε : 0 < ε) (Φ : A → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (Φ₁ : A → ℂ) (φ ψ : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ tsupport Φ₁ ⊆ tsupport Φ ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      tsupport φ ⊆ Set.Icc (-ε) ε ∧ tsupport ψ ⊆ Set.Icc (-ε) ε ∧
      ∀ x : A, Φ x = (∫ t, φ t * Φ₁ (x * NormedSpace.exp (t • X))) +
        ∫ t, ψ t * Φ (x * NormedSpace.exp (t • X)) := by sorry
