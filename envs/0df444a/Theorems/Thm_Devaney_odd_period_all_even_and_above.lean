-- Prove2me | Theorems.Thm_Devaney_odd_period_all_even_and_above
-- name    : Devaney.odd_period_all_even_and_above
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-17T14:22:44.773422+00:00
-- url     : https://prove2.me/theorems/c9dcff66-8b2e-4521-80b8-cb571d05d3cc
-- title:
--   An odd period forces all even periods and all larger periods
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be continuous and suppose $f$ has a periodic point whose least period $m$ is odd with $m\ge 3$. Then:
--
--   1. $f$ has a periodic point of least period $n$ for **every even** $n\ge 2$; and
--   2. $f$ has a periodic point of least period $n$ for **every** $n\ge m+1$.
--
--   $$m \text{ odd},\ m\ge 3 \quad\Longrightarrow\quad \{\,n \text{ even}\,\}\cup\{\,n\ge m+1\,\}\subseteq\{\text{least periods of } f\}.$$
--
--   This is the substantial half of Sharkovsky's theorem. Together with the existence of a fixed point it accounts for every period that follows an odd $m>1$ in the Sharkovsky ordering: the odd numbers larger than $m$ and all even numbers, the latter covering both the numbers $2^{b}q$ with $q>1$ odd and the powers of two. The general case of Sharkovsky's theorem, for a period $p\cdot 2^{M}$ with $p>1$ odd, reduces to this statement by passing to the iterate $f^{2^{M}}$, which has least period $p$.
--
--   Clause (1) is the assertion that is genuinely hard: the even periods **smaller** than $m$ cannot be obtained from any loop built out of the given orbit alone, and require an auxiliary configuration of three intervals.
--
--   **Formalization Note** `HasPrimePeriod f x n` says $n$ is the least period of $x$. Evenness of $n$ is written as `n % 2 = 0`.
--
--   The source states the result for a continuous self-map of a compact interval; the statement here is for a continuous map of the whole real line, which is a weakening of the hypothesis. It remains valid because the argument only ever uses a covering relation $I\subseteq f(I)$, never the reverse inclusion $f(I)\subseteq I$.
-- source:
--   Bau-Sen Du, A Simple Proof of Sharkovsky's Theorem, arXiv:math/0606351v1 (2006), https://arxiv.org/abs/math/0606351, Section 3, Proposition 5.

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem odd_period_all_even_and_above (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) (hm : 3 ≤ m)
    (hodd : Odd m) (h : ∃ x, HasPrimePeriod f x m) :
    (∀ n : ℕ, 2 ≤ n → n % 2 = 0 → ∃ y, HasPrimePeriod f y n) ∧
    (∀ n : ℕ, m + 1 ≤ n → ∃ y, HasPrimePeriod f y n) := by sorry
end Devaney
