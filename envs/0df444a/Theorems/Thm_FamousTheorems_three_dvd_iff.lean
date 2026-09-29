-- Prove2me | Theorems.Thm_FamousTheorems_three_dvd_iff
-- name    : FamousTheorems.three_dvd_iff
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:18.103128+00:00
-- url     : https://prove2.me/theorems/e220dc42-a531-4864-a374-2c7c7f54a2af
-- title:
--   The divisibility-by-three rule
-- statement:
--   **A number is divisible by 3 iff its digit sum is.**
--
--   $$3 \mid n \iff 3 \mid \text{(sum of the decimal digits of } n).$$
--
--   Because $10 \equiv 1 \pmod 3$, every power of ten is $\equiv 1$, so
--   $n = \sum d_i 10^i \equiv \sum d_i \pmod 3$. The same argument gives the rule for $9$, since
--   $10 \equiv 1 \pmod 9$ too, and — using $10 \equiv -1 \pmod{11}$ — the alternating-sum rule for
--   $11$.
--
--   It is the most familiar instance of modular arithmetic in everyday use, and the basis of casting
--   out nines as an arithmetic check.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem three_dvd_iff : ∀ n : ℕ, 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum := by sorry

end FamousTheorems
