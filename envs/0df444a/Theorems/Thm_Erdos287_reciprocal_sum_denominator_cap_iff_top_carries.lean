-- Prove2me | Theorems.Thm_Erdos287_reciprocal_sum_denominator_cap_iff_top_carries
-- name    : Erdos287.reciprocal_sum_denominator_cap_iff_top_carries
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:38:51.391332+00:00
-- url     : https://prove2.me/theorems/b0e27096-e181-5e97-b353-1d68ca6f90bf
-- title:
--   One upper carry per prime characterizes a denominator cap
-- statement:
--   Let $L>0$ be a common multiple of all members of a finite set $D$, and let $C>0$. For each prime $p$ write $a=v_p(L)$ and $b=v_p(C)$. The reduced denominator of $\sum_{n\in D}1/n$ divides $C$ if and only if for every prime $p$, $p^{(a-b)_+}$ divides $\sum_{n\in D\, :\,v_p(n)>b}L/n$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reciprocal_sum_denominator_cap_iff_top_carries (D : Finset ℕ) (L C : ℕ) (hL : 0 < L) (hC : 0 < C)
    (hD : ∀ n ∈ D, n ∣ L) :
    (∑ n ∈ D, (1 : ℚ) / n).den ∣ C ↔
      ∀ p : ℕ, p.Prime →
        p ^ (L.factorization p - C.factorization p) ∣
          ∑ n ∈ D.filter (fun n => C.factorization p < n.factorization p), L / n := by sorry
