-- Prove2me | Theorems.Thm_Erdos1063_erdos_1063_variants_exception_dvd
-- name    : Erdos1063.erdos_1063.variants.exception_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:15:26.611109+00:00
-- url     : https://prove2.me/theorems/03fe7366-64e0-4a8c-97ec-eb505212e439
-- title:
--   variants: exception dvd
-- statement:
--   Structure of the exceptional index: if every $n - i$ with $i \ne e$ divides
--   $\binom{n}{k}$, then $e = n \bmod k$ and
--   $\prod_{p^a \| k} p^{a + v_p\binom{k-1}{e} + \lfloor \log_p \max(e, k-1-e) \rfloor}$
--   divides $n - e$.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Solution.lean#L42-L48
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Solution.lean#L42-L48

module
public import Definitions.Def_Erdos1063_Lower
public import Definitions.Def_Erdos1063_Solution
public import Theorems.Thm_Erdos1063_exception_dvd

set_option autoImplicit false
@[expose] public section
public section
open Erdos1063

theorem Erdos1063.erdos_1063.variants.exception_dvd {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e := by sorry
