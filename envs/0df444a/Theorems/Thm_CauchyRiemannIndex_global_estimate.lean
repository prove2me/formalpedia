-- Prove2me | Theorems.Thm_CauchyRiemannIndex_global_estimate
-- name    : CauchyRiemannIndex.global_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T21:01:58.045437+00:00
-- url     : https://prove2.me/theorems/6547bd5d-a57a-4144-8558-c8185a1448c3
-- title:
--   The global estimate for Cauchy–Riemann operators on the cylinder modulo a finite piece
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. Assume that the asymptotic operators $A^\pm=-J_0\partial_t-S^\pm(t)$ are nondegenerate. Then there are $R$ and $c$ such that
--   $$\|\eta\|_{W^{1,p}}\le c\,\|D_S\eta\|_{L^p}+c\,\|\eta\|_{L^p([-R,R]\times S^1)}$$
--   for every smooth $\eta$ on $\mathbb{R}\times S^1$ that vanishes for large $|s|$.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$. The estimate is stated for test sections $u$ (smooth, $1$-periodic in $t$, zero for large $|s|$), with $\|u\|_{W^{1,p}}$ = `w1pNorm p u` $=\|u\|_p+\|\partial_su\|_p+\|\partial_tu\|_p$ in `ℝ≥0∞` and $D_Su$ = `crOp S u`; the constant is in `ℝ≥0` and is chosen before $u$. $\|\eta\|_{L^p([-R,R]\times S^1)}$ is `eLpNorm u p (cylMeasure.restrict (Icc (-R) R ×ˢ univ))`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Lemma 4.13, p. 74 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lemma 4.13 (p. 74), case `k = 1`: let `D_S` be asymptotic to nondegenerate loops `S±`
of symmetric matrices and `1 < p < ∞`. There are `R` and `c` with
`‖η‖_{W^{1,p}} ≤ c ‖D_S η‖_{L^p} + c ‖η‖_{L^p([-R, R] × S¹)}` for every test section `η`. -/
theorem global_estimate (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure +
        c * eLpNorm u p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) := by
  sorry

end CauchyRiemannIndex
