-- Prove2me | Theorems.Thm_Erdos1063_sharp_valuation_bound
-- name    : Erdos1063.sharp_valuation_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:43.982406+00:00
-- url     : https://prove2.me/theorems/13d7cf2e-e8e9-5be2-9bf1-429df19953e2
-- title:
--   Erdos1063: sharp valuation bound
-- statement:
--   **The sharper exponent** (stated and proved by the user rickyc in the erdosproblems.com
--   thread, 10 July 2026; used by jbell31's search). If every `n - i` with `i ≠ e` divides
--   `C(n,k)` and `p ∣ k`, then
--   `v_p(k) + v_p(C(k-1,e)) + ⌊log_p max(e, k-1-e)⌋ ≤ v_p(n - e)`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L284-L376
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L284-L376

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.sharp_valuation_bound {n k p e : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e))
      ≤ padicValNat p (n - e) := by sorry
