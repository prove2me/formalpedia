-- Prove2me | Theorems.Thm_Erdos1063_erdos_1063_variants_lower_bound
-- name    : Erdos1063.erdos_1063.variants.lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:36:01.630445+00:00
-- url     : https://prove2.me/theorems/0c66347e-f862-44d4-8b5e-ce219cb3ba42
-- title:
--   variants: lower bound
-- statement:
--   Lower bound: for $k \ge 2$,
--   $n_k \ge \prod_{p^a \| k} p^{a + \lfloor \log_p (k-1) \rfloor}$.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Solution.lean#L34-L36
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Solution.lean#L34-L36

module
public import Definitions.Def_Erdos1063_Lower
public import Definitions.Def_Erdos1063_Solution
public import Theorems.Thm_Erdos1063_lower_bound

set_option autoImplicit false
@[expose] public section
public section
open Erdos1063

theorem Erdos1063.erdos_1063.variants.lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k := by sorry
