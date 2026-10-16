-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_subseq_cauchy_of_support_bounded
-- name    : CauchyRiemannIndex.exists_subseq_cauchy_of_support_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T07:59:51.02869+00:00
-- url     : https://prove2.me/theorems/b601cb21-4384-467b-a324-cebb6e192883
-- title:
--   Families of $C^1$ functions with common bounded support and bounded $W^{1,p}$ norm have a common $L^p$-Cauchy subsequence
-- statement:
--   Let $1\le p<\infty$, $r\in\mathbb R$, $M\ge0$, and let $\iota$ be a finite index set. For $k\in\mathbb N$ and $i\in\iota$ let $g_{k,i}:\mathbb R^m\to\mathbb R$ be continuously differentiable with
--   $$g_{k,i}(x)=0\ \text{ for }|x|>r,\qquad \|g_{k,i}\|_{L^p(\mathbb R^m)}\le M,\qquad \big\|\,\|Dg_{k,i}\|\,\big\|_{L^p(\mathbb R^m)}\le M.$$
--   Then there is a strictly increasing $\varphi:\mathbb N\to\mathbb N$ such that for every $i\in\iota$ the sequence $(g_{\varphi(k),i})_k$ is Cauchy in $L^p(\mathbb R^m)$.
--
--   This is the Rellich compactness property for $W^{1,p}$-bounded families with a common bounded support, for all $1\le p<\infty$ and every dimension, stated for finitely many component sequences at once so that it applies directly to vector-valued maps. It is the compact inclusion $W^{1,p}\hookrightarrow L^p$ on bounded regions used in Fredholm theory for elliptic operators.
--
--   **Formalization Note.** $p$ is in `ℝ≥0∞` and $M$ in `ℝ≥0`; $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)` with Lebesgue measure, $L^p$ norms are `eLpNorm`, $\|Dg\|$ is the operator norm of `fderiv ℝ g`, and $C^1$ is `ContDiff ℝ 1`. The Cauchy property is stated with $\varepsilon\in$ `ℝ≥0∞`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, p. 74 (the compact inclusion used after Lemma 4.13); standard Sobolev space theory, e.g. H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Proposition 9.3 and Theorem 9.16

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

/-- Let `1 ≤ p < ∞`, `r ∈ ℝ`, `M ≥ 0` and let `ι` be a finite index set. Let `g k i : ℝᵐ → ℝ`
(`k ∈ ℕ`, `i ∈ ι`) be `C¹` functions vanishing outside the closed ball of radius `r`, with
`‖g k i‖_{Lᵖ} ≤ M` and `‖ |D g k i| ‖_{Lᵖ} ≤ M`. Then there is one subsequence along which every
component sequence `k ↦ g k i` is Cauchy in `Lᵖ(ℝᵐ)`. -/
theorem exists_subseq_cauchy_of_support_bounded {m : ℕ} {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (r : ℝ) (M : ℝ≥0)
    (g : ℕ → ι → EuclideanSpace ℝ (Fin m) → ℝ) (hg : ∀ k i, ContDiff ℝ 1 (g k i))
    (hsupp : ∀ k i x, r < ‖x‖ → g k i x = 0)
    (hb : ∀ k i, eLpNorm (g k i) p volume ≤ M)
    (hdb : ∀ k i, eLpNorm (fun x => ‖fderiv ℝ (g k i) x‖) p volume ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N,
      eLpNorm (g (φ a) i - g (φ b) i) p volume < ε := by
  sorry

end CauchyRiemannIndex
