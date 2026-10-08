-- Prove2me | Theorems.Thm_CarryRNG_AWC_expansion_period_iff
-- name    : CarryRNG.AWC.expansion_period_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:16.692564+00:00
-- url     : https://prove2.me/theorems/58b135cd-2d18-47b1-ad2c-c67bdb65a7a9
-- title:
--   §4.1 — the base-$b$ expansion of $k/m$ is strictly periodic with period the order of $b$
-- statement:
--   Let $b \ge 2$ be a base and $m > 1$ a modulus with $\gcd(b, m) = 1$, and let $k$ be a reduced residue, $0 \le k < m$ with $\gcd(k, m) = 1$. Write $d_1, d_2, \dots$ for the base-$b$ digits of $k/m$ after the point, and $\operatorname{ord}_m(b)$ for the multiplicative order of $b$ modulo $m$. Then for every $p > 0$,
--
--   $$
--   \bigl(d_{j+p} = d_j \text{ for all } j \ge 1\bigr) \iff \operatorname{ord}_m(b) \mid p .
--   $$
--
--   In words: the expansion of $k/m$ is strictly periodic (periodic from the first digit after the point on), and its least period is exactly $\operatorname{ord}_m(b)$. This is the number-theoretic fact through which the periods of the add-with-carry generators are computed: once the generated digits are identified with those of some $k/m$, their period is the order of $b$.
--
--   **Formalization Note** The order is `orderOf (b : ZMod m)`. Stating the period as "$p$ is a period iff $\operatorname{ord}_m(b) \mid p$" pins down the least period, rather than only saying that $\operatorname{ord}_m(b)$ is a period.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.1

import Mathlib
import Definitions.Def_CarryRNG_AWC_digit

namespace CarryRNG.AWC

theorem expansion_period_iff (b m k : ℕ) (hb : 2 ≤ b) (hm : 1 < m) (hk : k < m)
    (hkm : Nat.Coprime k m) (hbm : Nat.Coprime b m) (p : ℕ) (hp : 0 < p) :
    (∀ j, 1 ≤ j → digit b m k (j + p) = digit b m k j) ↔ orderOf (b : ZMod m) ∣ p := by sorry

end CarryRNG.AWC
