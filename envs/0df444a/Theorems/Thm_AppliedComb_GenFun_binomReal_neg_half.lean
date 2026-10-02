-- Prove2me | Theorems.Thm_AppliedComb_GenFun_binomReal_neg_half
-- name    : AppliedComb.GenFun.binomReal_neg_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:12:09.661801+00:00
-- url     : https://prove2.me/theorems/7098b73c-9bbf-4352-bc45-9161a31becbb
-- title:
--   Lemma 8.12 — C(−1/2, k) = (−1)^k C(2k, k) / 2^{2k}
-- statement:
--   Let $\binom{p}{k} = P(p, k)/k!$ be the generalized binomial coefficient of Definition 8.9, for real $p$ and nonnegative integers $k$. Then for each integer $k \ge 0$,
--
--   $$\binom{-1/2}{k} = (-1)^k\,\frac{\binom{2k}{k}}{2^{2k}},$$
--
--   where $\binom{2k}{k}$ on the right is the ordinary (central) binomial coefficient. For example $\binom{-1/2}{1} = -\tfrac12 = -\tfrac{2}{4}$ and $\binom{-1/2}{2} = \tfrac38 = \tfrac{6}{16}$.
--
--   This closed form turns Newton's series for the exponent $-1/2$ into a series with integer coefficients, which is what Theorem 8.13 needs.
--
--   **Formalization Note.** The left side is `binomReal (-1 / 2) k` in $\mathbb{R}$; the central binomial coefficient is `Nat.choose (2 * k) k`, cast to $\mathbb{R}$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 167, Lemma 8.12

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

namespace AppliedComb.GenFun

/-- Keller–Trotter, Lemma 8.12 (p. 167): for each `k ≥ 0`,
`C(-1/2, k) = (-1)^k · C(2k, k) / 2^(2k)`, where `C(-1/2, k)` is the generalized binomial
coefficient of Definition 8.9 and `C(2k, k)` is the ordinary binomial coefficient. -/
theorem binomReal_neg_half (k : ℕ) :
    binomReal (-1 / 2) k = (-1) ^ k * ((Nat.choose (2 * k) k : ℕ) : ℝ) / 2 ^ (2 * k) := by sorry

end AppliedComb.GenFun
