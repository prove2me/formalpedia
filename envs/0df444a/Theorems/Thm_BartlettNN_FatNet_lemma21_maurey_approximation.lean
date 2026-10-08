-- Prove2me | Theorems.Thm_BartlettNN_FatNet_lemma21_maurey_approximation
-- name    : BartlettNN.FatNet.lemma21_maurey_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:25:19.827778+00:00
-- url     : https://prove2.me/theorems/04a20372-de8c-48cc-a4a8-0e7e62bef808
-- title:
--   Lemma 21 (Maurey) — ‖h − (1/k)Σ f_i‖² ≤ c/k for h in the closed convex hull
-- statement:
--   Let $G$ be a real Hilbert space and $F\subseteq G$ with $\|f\|\le b$ for all $f\in F$. Let $h$ be an element of the closure of the convex hull of $F$. Then for every integer $k\ge1$ and every real $c>b^2-\|h\|^2$ there are $f_1,\dots,f_k\in F$ (not necessarily distinct) such that
--
--   $$
--   \Big\|h-\frac1k\sum_{i=1}^k f_i\Big\|^2\ \le\ \frac ck .
--   $$
--
--   The approximation error depends on $k$ and the bound $b$ but not on the dimension of $G$ or on how many elements of $F$ are needed to represent $h$ exactly. In the paper it yields $\ell_2$ covers of the network class from covers of the hidden-unit class (Lemma 22). The paper attributes it to Maurey and does not prove it.
--
--   **Formalization Note** $G$ is a complete real inner product space. "Convex closure" is read as the topological closure of the convex hull. The $f_i$ form a family indexed by $\{0,\dots,k-1\}$, so repetitions are allowed, as in the paper's $\{f_1,\dots,f_k\}\subseteq F$.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Lemma 21 (attributed to Maurey, see [4], [24])

import Mathlib

namespace BartlettNN.FatNet

/-- **Lemma 21** (Maurey; Bartlett 1998, p. 532).
Let `G` be a (real) Hilbert space and `F ⊆ G` with `‖f‖ ≤ b` for all `f ∈ F`. Let `h` lie in
the closure of the convex hull of `F`. Then for every `k ≥ 1` and every `c > b² − ‖h‖²` there
are `f_1, …, f_k ∈ F` (repetitions allowed) with `‖h − (1/k) ∑ f_i‖² ≤ c/k`. -/
theorem lemma21_maurey_approximation {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (F : Set G) (b : ℝ) (hb : ∀ f ∈ F, ‖f‖ ≤ b)
    (h : G) (hh : h ∈ closure (convexHull ℝ F)) :
    ∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, b ^ 2 - ‖h‖ ^ 2 < c →
      ∃ f : Fin k → G, (∀ i, f i ∈ F) ∧ ‖h - (k : ℝ)⁻¹ • ∑ i, f i‖ ^ 2 ≤ c / k := by sorry

end BartlettNN.FatNet
