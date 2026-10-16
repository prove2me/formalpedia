-- Prove2me | Theorems.Thm_CauchyRiemannIndex_eLpNorm_translate_sub_le
-- name    : CauchyRiemannIndex.eLpNorm_translate_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T07:59:49.89198+00:00
-- url     : https://prove2.me/theorems/67d0148b-a528-4693-828c-f09c3e47e04f
-- title:
--   The $L^p$ norm of a translation difference of a $C^1$ function is bounded by $|h|\,\|Dg\|_{L^p}$
-- statement:
--   Let $1\le p<\infty$, let $F$ be a real Banach space, let $g:\mathbb R^m\to F$ be continuously differentiable, and let $h\in\mathbb R^m$. Then
--   $$\Big(\int_{\mathbb R^m}\big|g(x+h)-g(x)\big|^p\,dx\Big)^{1/p}\;\le\;|h|\,\Big(\int_{\mathbb R^m}\|Dg(x)\|^p\,dx\Big)^{1/p},$$
--   where $\|Dg(x)\|$ is the operator norm of the derivative of $g$ at $x$.
--
--   This is the standard modulus-of-continuity bound for translations in $L^p$ in terms of the gradient. It gives equicontinuity of translations, uniformly over families with bounded $W^{1,p}$ norm, and is used for compactness statements for Sobolev-bounded families. No integrability of $g$ or $Dg$ is assumed; the right-hand side may be infinite.
--
--   **Formalization Note.** $p$ is in `ℝ≥0∞`; norms are written with `eLpNorm` for Lebesgue measure on `EuclideanSpace ℝ (Fin m)`, $|h|$ is `ENNReal.ofReal ‖h‖`, $Dg$ is `fderiv ℝ g` and $C^1$ is `ContDiff ℝ 1`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, p. 74 (the compact inclusion used after Lemma 4.13); standard Sobolev space theory, e.g. H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Proposition 9.3 and Theorem 9.16

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

/-- For `1 ≤ p < ∞` and a `C¹` map `g : ℝᵐ → F` into a Banach space, the `Lᵖ` norm of the
translation difference `x ↦ g (x + h) - g x` is at most `|h|` times the `Lᵖ` norm of `|Dg|`. -/
theorem eLpNorm_translate_sub_le {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin m) → F) (hg : ContDiff ℝ 1 g) (h : EuclideanSpace ℝ (Fin m)) :
    eLpNorm (fun x => g (x + h) - g x) p volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm (fun x => ‖fderiv ℝ g x‖) p volume := by
  sorry

end CauchyRiemannIndex
