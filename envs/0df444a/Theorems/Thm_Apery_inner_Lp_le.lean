-- Prove2me | Theorems.Thm_Apery_inner_Lp_le
-- name    : Apery.inner_Lp_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:24:12.528964+00:00
-- url     : https://prove2.me/theorems/886bbb34-830a-4629-8274-f178860de747
-- title:
--   Inner per-prime bound, discrete form: $-L_p \le -2h\lfloor K/p\rfloor + 12h\lfloor N/p\rfloor + 2T(h) - hk + 2\sum_c \psi + (k-k_0)L_0 + 2B_0 + 1$
-- statement:
--   For $n \ge 33$, odd $p \ge 7$ with $3p \le 40n$, $2\cdot 40n < p^2$ and the degree condition, and every level $k$ in the admissible window $[k_0, k_{\mathrm top}]$, the local exponent satisfies
--
--   $$-L_p \;\le\; -2h\Bigl\lfloor\frac{K}{p}\Bigr\rfloor + 12h\Bigl\lfloor\frac{N}{p}\Bigr\rfloor + 2T(h) - h\,k + 2\sum_{c=1}^{p/2} \psi\bigl(k, B + 6a'_c - a_c\bigr) + (k-k_0)L_0 + 2B_0 + 1,$$
--
--   with $K = 40n$, $N = 3n$, $h = 37n$, $T$ the layer-cake function, $B = 12\lfloor N/p\rfloor - 2\lfloor K/p\rfloor - 4$ and $a_c, a'_c$ the class counts. This is `inner_Lp_le` of `Apery/Growth/InnerPrime.lean` (discrete form). **Formalization Note** `Lp`, `layer`, `hIn`, `aCnt`, `Bmax`, `kloI`, `ktopI`, `L0I`, `Mcut` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerPrime.lean#L179-L263

import Mathlib
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceGrowthErrors

open Finset

namespace Apery

theorem inner_Lp_le {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (hn : 33 ≤ n)
    (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p) (hsmall : ¬ p * Mcut ≤ 40 * n)
    (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (k : ℤ) (hk1 : kloI n p ≤ k) (hk2 : k ≤ ktopI n p) :
    -(Lp n p : ℝ) ≤ -2 * (37 * n : ℕ) * ((40 * n / p : ℕ) : ℝ) +
      12 * (37 * n : ℕ) * ((3 * n / p : ℕ) : ℝ) + 2 * layer p 1000 (37 * n : ℕ) -
      (37 * n : ℕ) * (k : ℝ) +
      2 * ∑ c ∈ Icc 1 (p / 2), hIn n p k (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c) +
      ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 := by
  sorry

end Apery
