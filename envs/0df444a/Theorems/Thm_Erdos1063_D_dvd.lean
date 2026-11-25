-- Prove2me | Theorems.Thm_Erdos1063_D_dvd
-- name    : Erdos1063.D_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:48.366623+00:00
-- url     : https://prove2.me/theorems/83c864f7-8574-534c-830c-b44a6d6beda6
-- title:
--   Erdos1063: D dvd
-- statement:
--   rickyc's divisibility in product form: `D(k,e) = ∏_{p^a ∥ k}
--   p^(a + v_p(C(k-1,e)) + ⌊log_p max(e,k-1-e)⌋)` divides `n - e`. Together with
--   `index_eq_mod` this is exactly the structural input of jbell31's exhaustive search.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L381-L391
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L381-L391

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.D_dvd {n k e : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    (∏ p ∈ k.primeFactors,
      p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e))))
      ∣ n - e := by sorry
