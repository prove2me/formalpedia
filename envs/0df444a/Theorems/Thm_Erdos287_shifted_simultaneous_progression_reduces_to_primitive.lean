-- Prove2me | Theorems.Thm_Erdos287_shifted_simultaneous_progression_reduces_to_primitive
-- name    : Erdos287.shifted_simultaneous_progression_reduces_to_primitive
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T19:55:51.346651+00:00
-- url     : https://prove2.me/theorems/19b5f217-5f84-4cd9-8b7c-0960153ff616
-- title:
--   Primitive progression after normalizing a shifted simultaneous congruence
-- statement:
--   Let $mq>0$, $s\ne0$, $\gcd(m,q)=\gcd(s,mq)=1$, and suppose $s\mid mn-a$ and $mn\equiv A\bmod q$. Put $w=(mn-a)/s$ and $g=\gcd(a,m)\gcd(A-a,q)$. Then $g=\gcd(w,mq)>0$ in the sense that $g$ divides both $w$ and $mq$, and $w/g$ is coprime to $mq/g$. For every integer $t$ the normalized shifted value along $n+qst$ equals $w/g+(mq/g)t$.
-- source:
--   Arithmetic normalization for the Erdős #287 Type II remainder. See Zheng, Primes in simultaneous arithmetic progressions, https://arxiv.org/html/2512.22798v1#S3.

import Mathlib

theorem Erdos287.shifted_simultaneous_progression_reduces_to_primitive (m q s n a A : ℤ) (hmq : 0 < m * q) (hs : s ≠ 0)
    (hcop : IsCoprime m q) (hscop : IsCoprime s (m * q))
    (hdiv : s ∣ m * n - a) (hA : m * n ≡ A [ZMOD q]) :
    let w := (m * n - a) / s
    let g : ℤ := ↑(a.gcd m * (A - a).gcd q)
    0 < g ∧ g ∣ w ∧ g ∣ m * q ∧ IsCoprime (w / g) (m * q / g) ∧
      ∀ t : ℤ, (m * (n + q * s * t) - a) / s / g =
        w / g + (m * q / g) * t := by sorry
