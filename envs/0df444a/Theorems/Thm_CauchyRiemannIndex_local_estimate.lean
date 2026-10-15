-- Prove2me | Theorems.Thm_CauchyRiemannIndex_local_estimate
-- name    : CauchyRiemannIndex.local_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T21:01:10.166302+00:00
-- url     : https://prove2.me/theorems/83cff4e0-71c9-4d18-a232-f02522ea767c
-- title:
--   The local elliptic estimate for Cauchy–Riemann operators on a finite cylinder
-- statement:
--   Let $1<p<\infty$, $R\in\mathbb{R}$, and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous. There is a constant $c$ such that
--   $$\|\eta\|_{W^{1,p}}\le c\,\|D_S\eta\|_{L^p}+c\,\|\eta\|_{L^p}$$
--   for every smooth $\eta$ on $\mathbb{R}\times S^1$ that vanishes for $|s|\ge R$.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞`. $S$ is continuous and $1$-periodic in $t$. The estimate is stated for test sections $u$ (smooth, $1$-periodic in $t$, zero for large $|s|$), with $\|u\|_{W^{1,p}}$ = `w1pNorm p u` $=\|u\|_p+\|\partial_su\|_p+\|\partial_tu\|_p$ in `ℝ≥0∞` and $D_Su$ = `crOp S u`; the constant is in `ℝ≥0` and is chosen before $u$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Proposition 4.8, p. 71 (case k = 1, Σ₀ = [-R, R] × S¹)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Proposition 4.8 (p. 71), case `k = 1`, on the compact piece `[-R, R] × S¹` of the
cylinder: for `1 < p < ∞` and a continuous `t`-periodic `S` there is `c` with
`‖η‖_{W^{1,p}} ≤ c ‖D_S η‖_{L^p} + c ‖η‖_{L^p}` for every smooth `η`, `1`-periodic in `t`,
that vanishes for `|s| ≥ R`. -/
theorem local_estimate (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ)
    (S : ℝ × ℝ → Mat n) (hS : Continuous S) (hper : ∀ s t, S (s, t + 1) = S (s, t)) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → (∀ s t, R ≤ |s| → u (s, t) = 0) →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure + c * eLpNorm u p cylMeasure := by
  sorry

end CauchyRiemannIndex
