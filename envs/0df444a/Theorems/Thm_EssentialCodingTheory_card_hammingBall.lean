-- Prove2me | Theorems.Thm_EssentialCodingTheory_card_hammingBall
-- name    : EssentialCodingTheory.card_hammingBall
-- status  : Open
-- author  : @chaikon
-- created : 2026-10-14T16:41:35.606792+00:00
-- url     : https://prove2.me/theorems/270af476-5ef0-47a7-9b52-3840c35283a5
-- title:
--   Volume of a Hamming ball: $|B(x,e)| = \sum_{i \le e} \binom{n}{i}(q-1)^i$
-- statement:
--   Let $\alpha$ be a finite alphabet with $q = |\alpha|$ symbols, and let $n \ge 0$. For a word $x \in \alpha^n$ and a radius $e \ge 0$, the Hamming ball $B(x, e)$ is the set of words $y \in \alpha^n$ that differ from $x$ in at most $e$ coordinates. Its size is
--
--   $$|B(x, e)| = \sum_{i=0}^{e} \binom{n}{i} (q-1)^i.$$
--
--   The $i$-th term counts the words at distance exactly $i$ from $x$: choose the $i$ differing coordinates, then one of the $q - 1$ other symbols in each.
-- source:
--   V. Guruswami, A. Rudra, M. Sudan, Essential Coding Theory (web draft), https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf, §1.7, p. 21, equation (1.18) in the proof of Theorem 1.7.2; Hamming ball from Definition 1.6.1, p. 19.

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Finset

namespace EssentialCodingTheory
theorem card_hammingBall {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (e : ℕ) :
    (univ.filter fun y : Fin n → α => hammingDist x y ≤ e).card =
      ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i := by sorry
end EssentialCodingTheory
