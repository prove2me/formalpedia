-- Prove2me | Theorems.Thm_Antihydra_nonneg_first_100000
-- name    : Antihydra.nonneg_first_100000
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:12:44.936238+00:00
-- url     : https://prove2.me/theorems/fa57100b-027b-4e6c-8387-2a04df15b2f1
-- title:
--   Antihydra: the parity counter stays nonnegative for the first 100,000 steps
-- statement:
--   Let $a_0 = 8$ and $a_{n+1} = \lfloor 3a_n/2 \rfloor$, and let $b_0 = 0$, $b_{n+1} = b_n + 2$ if $a_n$ is even and $b_{n+1} = b_n - 1$ if $a_n$ is odd. Then $b_n \ge 0$ for every $n \le 100\,000$.
--
--   This is the bounded, finitely checkable case of the open Antihydra problem (`Antihydra.cumulative_odd_never_more_than_twice_even`), which asserts $b_n \ge 0$ for **all** $n$; equivalently, the 6-state Busy Beaver candidate machine *Antihydra* does not halt within the corresponding number of Collatz-like rule applications. It is a partial step toward the open problem: it provides verified evidence, not a proof of it.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean (Antihydra); bbchallenge.org Antihydra cryptid

namespace Antihydra
theorem nonneg_first_100000
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, n ≤ 100000 → b n ≥ 0 := by
  sorry
end Antihydra
