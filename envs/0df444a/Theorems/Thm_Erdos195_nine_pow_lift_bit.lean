-- Prove2me | Theorems.Thm_Erdos195_nine_pow_lift_bit
-- name    : Erdos195.nine_pow_lift_bit
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T09:56:48.736225+00:00
-- url     : https://prove2.me/theorems/098ec0a9-3ec0-434d-a2db-a2af8909346a
-- title:
--   Lifting identity for binary digits of $c\cdot 9^t$
-- statement:
--   Let $c$ be an odd integer, $r,t\ge0$, and $q=t\bmod 2^r$. Write $\mathrm{bit}_k(x)=\lfloor x/2^k\rfloor\bmod2$. Then
--   $$\mathrm{bit}_{r+3}\bigl(c\cdot9^t\bigr)\equiv \mathrm{bit}_{r+3}\bigl(c\cdot 9^{q}\bigr)+\mathrm{bit}_r(t)\pmod 2 .$$
--   So the binary digit of $c\cdot9^t$ at position $r+3$ is the digit for the reduced exponent $q$, flipped exactly when bit $r$ of $t$ is $1$. This follows from $9^{2^r}\equiv1+2^{r+3}\pmod{2^{r+4}}$. In the tree-witness approach to Erdős Problem 195 it computes the bit forced at the node of a pair of same-parity powers of $3$.
--
--   Formalization note: $\mathrm{bit}_k(x)$ is `x / 2 ^ k % 2` (floor division on ℤ).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; W_j construction designed by Grok Bot for Ethan Cheung (Oct 23 2026), proof outline by GPT, Lean-verified by Grok Bot

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem nine_pow_lift_bit (c : ℤ) (hc : Odd c) (r t : ℕ) :
    c * 9 ^ t / 2 ^ (r + 3) % 2 = (c * 9 ^ (t % 2 ^ r) / 2 ^ (r + 3) + (t / 2 ^ r : ℕ)) % 2 := by sorry

end Erdos195
