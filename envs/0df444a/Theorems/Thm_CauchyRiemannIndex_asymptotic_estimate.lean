-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptotic_estimate
-- name    : CauchyRiemannIndex.asymptotic_estimate
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:01:21.885958+00:00
-- url     : https://prove2.me/theorems/e7a7f80b-6161-4980-b7b2-6034452d56da
-- title:
--   The elliptic estimate on cylindrical ends with nondegenerate asymptotics
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. If $A^+=-J_0\partial_t-S^+$ is nondegenerate, there are $R$ and $c$ such that
--   $$\|\eta\|_{W^{1,p}}\le c\,\|D_S\eta\|_{L^p}$$
--   for every smooth $\eta$ that vanishes for $s\le R$. Likewise, if $A^-$ is nondegenerate, there are $R$ and $c$ such that the same estimate holds for every $\eta$ that vanishes for $s\ge-R$.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$. The estimate is stated for test sections $u$ (smooth, $1$-periodic in $t$, zero for large $|s|$), with $\|u\|_{W^{1,p}}$ = `w1pNorm p u` $=\|u\|_p+\|\partial_su\|_p+\|\partial_tu\|_p$ in `ℝ≥0∞` and $D_Su$ = `crOp S u`; the constant is in `ℝ≥0` and is chosen before $u$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Proposition 4.9, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Proposition 4.9 (p. 71), case `k = 1`: let `D_S` be asymptotic to loops `S±` of
symmetric matrices and `1 < p < ∞`. If `S⁺` is nondegenerate, there are `R` and `c` with
`‖η‖_{W^{1,p}} ≤ c ‖D_S η‖_{L^p}` for every test section `η` vanishing for `s ≤ R`; likewise at
the negative end when `S⁻` is nondegenerate, for `η` vanishing for `s ≥ -R`. -/
theorem asymptotic_estimate (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) :
    (IsNondegenerate Splus → ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∀ s t, s ≤ R → u (s, t) = 0) → w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure) ∧
    (IsNondegenerate Sminus → ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∀ s t, -R ≤ s → u (s, t) = 0) → w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure) := by
  sorry

end CauchyRiemannIndex
