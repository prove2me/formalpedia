-- Prove2me | Theorems.Thm_CauchyRiemannIndex_compact_restriction
-- name    : CauchyRiemannIndex.compact_restriction
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:02:15.728563+00:00
-- url     : https://prove2.me/theorems/4c0640bd-be9d-4105-8d88-ef7b2b46d35a
-- title:
--   Compactness of the restriction from W^{1,p} to L^p of a finite cylinder
-- statement:
--   Let $1<p<\infty$ and $R\in\mathbb{R}$. Every sequence of smooth maps on $\mathbb{R}\times S^1$ that vanish for large $|s|$ and are bounded in $W^{1,p}$ has a subsequence that is Cauchy in $L^p([-R,R]\times S^1)$.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞`. The sequence consists of test sections $u_k$ with `w1pNorm p (u k) ≤ 1`; the conclusion gives a strictly increasing $\varphi:\mathbb{N}\to\mathbb{N}$ such that $\|u_{\varphi(i)}-u_{\varphi(j)}\|_{L^p([-R,R]\times[0,1))}\to0$, written with $\varepsilon\in$ `ℝ≥0∞`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, p. 74 (the compact inclusion used after Lemma 4.13)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, p. 74 (the compact inclusion `W^{1,p}(Σ_R) ↪ L^p(Σ_R)` used after Lemma 4.13), on
`Σ_R = [-R, R] × S¹`: for `1 < p < ∞`, every sequence of test sections bounded in `W^{1,p}`
has a subsequence that is Cauchy in `L^p([-R, R] × S¹)`. -/
theorem compact_restriction (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ)
    (u : ℕ → ℝ × ℝ → Vec n) (hu : ∀ k, IsTestSection (u k)) (hb : ∀ k, w1pNorm p (u k) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      eLpNorm (u (φ i) - u (φ j)) p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) < ε := by
  sorry

end CauchyRiemannIndex
