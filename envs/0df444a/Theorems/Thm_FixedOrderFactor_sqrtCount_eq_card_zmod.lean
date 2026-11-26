-- Prove2me | Theorems.Thm_FixedOrderFactor_sqrtCount_eq_card_zmod
-- name    : FixedOrderFactor.sqrtCount_eq_card_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:13.040839+00:00
-- url     : https://prove2.me/theorems/c044636e-a734-58b2-9552-b39d2c7d5b5b
-- title:
--   Fixed Order Factor: sqrt Count eq card zmod
-- statement:
--   **The residue-class reading.** For `M > 0` and `s ∣ M`, `β(M, a, s)` counts the units `y` of
--   `ℤ/M` with `y² = a` and `y ≡ -1 (mod s)`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L186-L189
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L186-L189

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sqrtCount_eq_card_zmod {M : ℕ} [NeZero M] {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    sqrtCount M a s = (Finset.univ.filter fun y : ZMod M =>
      IsUnit y ∧ y ^ 2 = a ∧ ZMod.castHom hs (ZMod s) y = -1).card := by sorry
