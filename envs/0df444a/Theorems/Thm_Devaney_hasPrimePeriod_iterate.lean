-- Prove2me | Theorems.Thm_Devaney_hasPrimePeriod_iterate
-- name    : Devaney.hasPrimePeriod_iterate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-17T14:22:29.491922+00:00
-- url     : https://prove2.me/theorems/dd82986a-653f-4791-adce-6d37642aba2d
-- title:
--   Least period under an iterate: $m/\gcd(m,n)$
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ and let $x$ be a periodic point of $f$ of least period $m$. For every $n\ge 1$, the same point $x$ is periodic for the iterate $f^{n}$, with least period
--
--   $$\frac{m}{\gcd(m,n)}.$$
--
--   This is the basic bookkeeping rule relating the periodic orbits of a map to those of its iterates, and it is used constantly in the proof of Sharkovsky's theorem, where one repeatedly replaces $f$ by $f^{2^{a}}$ in order to strip powers of two off a period. Note that no continuity is needed: the statement is purely about the orbit structure of an arbitrary self-map.
--
--   **Formalization Note** `HasPrimePeriod f x n` says $n$ is the least period of $x$, and `f^[n]` is the $n$-fold iterate of `f`.
-- source:
--   Bau-Sen Du, A Simple Proof of Sharkovsky's Theorem, arXiv:math/0606351v1 (2006), https://arxiv.org/abs/math/0606351, Section 1, Lemma 1(1); Du attributes it to L. S. Block and W. A. Coppel, Dynamics in One Dimension, Lecture Notes in Math. 1513, Springer, 1992, page 12.

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem hasPrimePeriod_iterate (f : ℝ → ℝ) (x : ℝ) (m n : ℕ) (hn : 0 < n)
    (h : HasPrimePeriod f x m) : HasPrimePeriod (f^[n]) x (m / Nat.gcd m n) := by sorry
end Devaney
