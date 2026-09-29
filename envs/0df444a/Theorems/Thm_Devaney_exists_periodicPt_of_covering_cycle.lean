-- Prove2me | Theorems.Thm_Devaney_exists_periodicPt_of_covering_cycle
-- name    : Devaney.exists_periodicPt_of_covering_cycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-17T14:21:04.040043+00:00
-- url     : https://prove2.me/theorems/be4bcfc2-5771-4da7-8382-935c2763c97c
-- title:
--   A cycle of covering intervals carries a periodic point following it
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be continuous and let $J_0,J_1,\dots,J_{n-1},J_n=J_0$ be closed bounded intervals forming a **cycle of coverings**, that is
--
--   $$J_0\to J_1\to\cdots\to J_{n-1}\to J_0,\qquad\text{where } I\to J \text{ means } J\subseteq f(I).$$
--
--   Then $f$ has a point $y$ that *follows the loop*:
--
--   1. $f^{n}(y)=y$, so $y$ is a periodic point whose period divides $n$; and
--   2. $f^{i}(y)\in J_i$ for every $0\le i<n$.
--
--   This is the central existence tool of one-dimensional combinatorial dynamics. Every construction of a periodic point of a prescribed period for an interval map proceeds by exhibiting a suitable loop of intervals and invoking this statement; the itinerary condition (2) is what allows one to afterwards rule out the proper divisors of $n$ and conclude that the least period is exactly $n$.
--
--   **Formalization Note** The cycle is encoded by two sequences of endpoints with $a_n=a_0$ and $b_n=b_0$, so that $J_i=[a_i,b_i]$ closes up after $n$ steps. `Set.uIcc x y` is the closed interval with endpoints $x,y$ in either order, so no ordering hypothesis on endpoints is required.
-- source:
--   Bau-Sen Du, A Simple Proof of Sharkovsky's Theorem, arXiv:math/0606351v1 (2006), https://arxiv.org/abs/math/0606351, Section 3, Lemma 4. See also V. L. Smirnov and J. J. Tolosa, The Sharkovsky Theorem, arXiv:1702.07964v1 (2017), https://arxiv.org/abs/1702.07964, Section 5, Lemma 4 (Itinerary Lemma), part 1, page 11.

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem exists_periodicPt_of_covering_cycle (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (hn : 0 < n) (a b : ℕ → ℝ)
    (hcov : ∀ i < n, Covers f (Set.uIcc (a i) (b i)) (Set.uIcc (a (i + 1)) (b (i + 1))))
    (ha : a n = a 0) (hb : b n = b 0) :
    ∃ y : ℝ, f^[n] y = y ∧ ∀ i < n, f^[i] y ∈ Set.uIcc (a i) (b i) := by sorry
end Devaney
