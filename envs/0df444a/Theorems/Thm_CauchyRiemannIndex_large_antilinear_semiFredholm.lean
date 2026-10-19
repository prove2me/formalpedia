-- Prove2me | Theorems.Thm_CauchyRiemannIndex_large_antilinear_semiFredholm
-- name    : CauchyRiemannIndex.large_antilinear_semiFredholm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T13:34:24.969609+00:00
-- url     : https://prove2.me/theorems/b16f2515-bc72-48ff-932f-65aeac5d7978
-- title:
--   Semi-Fredholm property of Cauchy–Riemann operators with a large antilinear zeroth-order term
-- statement:
--   Let $n=1$, let $S^\pm$ be continuous loops of symmetric $2\times2$ matrices, and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2\times2}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$. Let $\beta:\mathbb{R}\times S^1\to\mathbb{C}$ be smooth with bounded first derivative, such that $|\beta|$ and $1/|\beta|$ are bounded for large $|s|$: there are $R$ and $c>0$ with $c\le|\beta(s,t)|\le 1/c$ whenever $|s|\ge R$. For $\sigma\in\mathbb{R}$ let $D_\sigma\eta=\partial_s\eta+J_0\partial_t\eta+S\eta+\sigma\beta\bar\eta$, acting from $W^{1,2}(\mathbb{R}\times S^1,\mathbb{C})$ to $L^2(\mathbb{R}\times S^1,\mathbb{C})$.
--
--   Then there is $\sigma_0$ such that for every $\sigma\ge\sigma_0$ the operator $D_\sigma$ is semi-Fredholm: its kernel is finite-dimensional and its range is closed in $L^2$.
--
--   No nondegeneracy of the asymptotic operators of $S^\pm$ is assumed, and nothing is assumed about the zeros of $\beta$ in the region $|s|<R$. This is the setting of Wendl's § 5.5 (operators $D_S+\sigma\beta\,\overline{\,\cdot\,}$ with a large antilinear zeroth-order term); closedness of the range is what allows the cokernel of $D_\sigma$ to be identified with the annihilator of its range.
--
--   **Formalization Note** $\mathbb{C}=\mathbb{R}^2$ via $(x,y)\mapsto x+iy$, and $\eta\mapsto\beta\bar\eta$ is the matrix `antilinearMat β`, so $D_\sigma$ is $D_{S_\sigma}$ with $S_\sigma=S+\sigma\cdot$`antilinearMat ∘ β`. Points of the cylinder are pairs $(s,t)$ and $\beta$ is $1$-periodic in $t$. $W^{1,2}$, the kernel `crKernel 2` and the range `crRange 2` are those of `Definitions.Def_CauchyRiemannIndex_Setting`. The hypotheses on $S$, $S^\pm$ and $\beta$ are a subset of those of the milestone `CauchyRiemannIndex.large_antilinear_perturbation_index` (Wendl, Proposition 5.27). The exponent is $p=2$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, setting of § 5.5, p. 94 (cylinder, trivial line bundle, p = 2)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Semi-Fredholm property of `D_σ η = D_S η + σ β η̄` for large `σ` (Wendl, § 5.5, p. 94, on the
cylinder with the trivial line bundle and `p = 2`, `n = 1`): let `S` be asymptotic to loops `S±`
of symmetric matrices, and let `β : ℝ × S¹ → ℂ` be smooth with bounded derivative, with `|β|` and
`1/|β|` bounded for large `|s|`. Then for all large `σ`, `D_σ : W^{1,2} → L²` has
finite-dimensional kernel and closed range. -/
theorem large_antilinear_semiFredholm (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      IsClosed (crRange 2 (fun x => S x + σ • antilinearMat (β x)) : Set (LpCyl 1 2)) := by
  sorry

end CauchyRiemannIndex
