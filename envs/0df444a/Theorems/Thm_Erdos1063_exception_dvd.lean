-- Prove2me | Theorems.Thm_Erdos1063_exception_dvd
-- name    : Erdos1063.exception_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:09.181991+00:00
-- url     : https://prove2.me/theorems/4feb424f-fbae-4c8d-960b-6420ef86d606
-- title:
--   Erdos1063: exception dvd
-- statement:
--   Structure of the exceptional index: if every $n - i$ with $i \ne e$ divides
--   $\binom{n}{k}$, then $e = n \bmod k$ and
--   $\prod_{p^a \| k} p^{a + v_p\binom{k-1}{e} + \lfloor \log_p \max(e, k-1-e) \rfloor}$
--   divides $n - e$.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L558-L564
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L558-L564

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.exception_dvd {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e := by sorry
