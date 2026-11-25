-- Prove2me | Theorems.Thm_Erdos1063_lower_bound
-- name    : Erdos1063.lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:57.077923+00:00
-- url     : https://prove2.me/theorems/f00a3da9-8424-5827-ae49-e17ecd0415a9
-- title:
--   Erdos1063: lower bound
-- statement:
--   Lower bound: for $k \ge 2$,
--   $n_k \ge \prod_{p^a \| k} p^{a + \lfloor \log_p (k-1) \rfloor}$.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L547-L552
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L547-L552

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k := by sorry
