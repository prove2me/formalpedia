-- Prove2me | Theorems.Thm_AbsConvexCombination_absConvexHull_eq_setOf_sum_smul
-- name    : AbsConvexCombination.absConvexHull_eq_setOf_sum_smul
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:42:51.068797+00:00
-- url     : https://prove2.me/theorems/6da3b2fd-daaf-4176-8cd0-09c1fe3635ba
-- title:
--   Absolutely convex hull $=$ finite combinations $\sum_i c_ix_i$ with $x_i\in A$, $\sum_i|c_i|\le 1$
-- statement:
--   **The absolutely convex hull as the set of finite absolutely convex combinations.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E$ be a $\mathbb K$-vector space and let $A\subset E$ be an arbitrary subset. A subset $D\subset E$ is *absolutely convex* (a *disk*, or *convex and circled*) if it is convex and balanced, i.e. $\lambda D\subset D$ for every $\lambda\in\mathbb K$ with $|\lambda|\le 1$. The *absolutely convex hull* (convex circled hull) $\Gamma(A)=\operatorname{cch}(A)$ is the smallest absolutely convex subset of $E$ containing $A$, i.e. the intersection of all absolutely convex subsets of $E$ containing $A$.
--
--   Then $\Gamma(A)$ consists exactly of the finite absolutely convex combinations of points of $A$:
--   $$\Gamma(A)=\Big\{\sum_{i=1}^{n} c_i\,x_i\ :\ n\ge 1,\ x_1,\dots,x_n\in A,\ c_1,\dots,c_n\in\mathbb K,\ \sum_{i=1}^{n}|c_i|\le 1\Big\}.$$
--   In particular $\Gamma(\emptyset)=\emptyset$, and $0\in\Gamma(A)$ whenever $A\neq\emptyset$.
--
--   This explicit description of disks is basic in the theory of locally convex spaces (Minkowski functionals, bounded disks, the projective tensor product topology). In the paper it is used in the proofs of Proposition 2.3.1.2(3) (p. 103) and Theorem 2.4.2.1 (p. 111): every element of a bounded set of Schwartz–Bruhat functions on $\mathbf A_{F,S}$ is written as a finite absolutely convex $\mathbf C$-linear combination of elementary tensors $f_\infty\otimes\bigotimes_{w\in S_f}f_w$, and estimates that are stable under such combinations are propagated from the elementary tensors to the whole bounded set.
--
--   **Formalization Note.** `absConvexHull 𝕜 s` is Mathlib's hull for `AbsConvex 𝕜 = Balanced 𝕜 ∧ Convex 𝕜`, with `[RCLike 𝕜]` (so $\mathbb K=\mathbb R$ or $\mathbb C$). Over $\mathbb C$, `Convex ℂ` refers to the partial order of `open scoped ComplexOrder` (`RCLike.toPartialOrder`), whose nonnegative elements are the nonnegative reals, so it is ordinary convexity; over $\mathbb R$ it is the usual order. The combinations are indexed by `Fin n` with `0 < n`, as in the source ($n\ge1$); allowing $n=0$ would put the empty sum $0$ into the right-hand side for $A=\emptyset$, where $\Gamma(\emptyset)=\emptyset$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 103, proof of Proposition 2.3.1.2(3) (also p. 111, proof of Theorem 2.4.2.1); classical reference: H. Jarchow, Locally Convex Spaces, Part I, Ch. 6, §6.1, p. 102 (case r = 1), and L. Narici and E. Beckenstein, Topological Vector Spaces, Thm. 4.2.11 (both as cited by the paper)

import Mathlib

open scoped ComplexOrder

set_option autoImplicit false

namespace AbsConvexCombination

/-- Over `𝕜 = ℝ` or `ℂ`, the absolutely convex hull of a set `s` in a `𝕜`-vector space is the set
of finite linear combinations `∑ cᵢ • xᵢ` of points `xᵢ ∈ s` with `∑ ‖cᵢ‖ ≤ 1`. -/
theorem absConvexHull_eq_setOf_sum_smul (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (s : Set E) :
    absConvexHull 𝕜 s =
      {y : E | ∃ (n : ℕ) (c : Fin n → 𝕜) (x : Fin n → E), 0 < n ∧ (∀ i, x i ∈ s) ∧
        ∑ i, ‖c i‖ ≤ 1 ∧ y = ∑ i, c i • x i} := by sorry

end AbsConvexCombination
