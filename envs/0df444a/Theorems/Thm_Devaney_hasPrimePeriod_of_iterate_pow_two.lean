-- Prove2me | Theorems.Thm_Devaney_hasPrimePeriod_of_iterate_pow_two
-- name    : Devaney.hasPrimePeriod_of_iterate_pow_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-17T14:22:34.164351+00:00
-- url     : https://prove2.me/theorems/ce91b677-ed07-42f5-b71a-2b481fb4f6b6
-- title:
--   Lifting an even period from $f^{2^M}$ back to $f$
-- statement:
--   Let $f:\mathbb R\to\mathbb R$, let $M\ge 0$, and suppose $y$ is a periodic point of the iterate $f^{2^{M}}$ whose least period $j$ is **even**. Then the least period of $y$ under $f$ itself is exactly
--
--   $$2^{M}\cdot j.$$
--
--   The converse direction of the bookkeeping rule for iterates is in general ambiguous: knowing the least period of $y$ under $f^{n}$ does not determine its least period under $f$. The hypothesis that $j$ be even removes the ambiguity in the case $n=2^{M}$, and this is precisely the form in which the rule is used to assemble Sharkovsky's theorem: every period one produces upstairs, for the map $f^{2^{M}}$, is arranged to be even so that it can be transported back to $f$ without loss.
--
--   **Formalization Note** `HasPrimePeriod f x n` says $n$ is the least period of $x$. No continuity is required.
-- source:
--   Bau-Sen Du, A Simple Proof of Sharkovsky's Theorem, arXiv:math/0606351v1 (2006), https://arxiv.org/abs/math/0606351, Section 1, Lemma 1(2), specialised to n = 2^M with k even: there s divides 2^M and is coprime to the even number k, forcing s = 1 and least period k*2^M. This is the form in which Lemma 1(2) is applied in Section 4, proof of Theorem 6.

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem hasPrimePeriod_of_iterate_pow_two (f : ℝ → ℝ) (y : ℝ) (M j : ℕ) (hj : 2 ∣ j)
    (h : HasPrimePeriod (f^[2 ^ M]) y j) : HasPrimePeriod f y (2 ^ M * j) := by sorry
end Devaney
