-- Prove2me | Theorems.Thm_FixedOrderFactor_sqrtCount_imaginary
-- name    : FixedOrderFactor.sqrtCount_imaginary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:51.91569+00:00
-- url     : https://prove2.me/theorems/b7efe49a-f8df-583d-ac25-22f8c63a3978
-- title:
--   Fixed Order Factor: sqrt Count imaginary
-- statement:
--   **Imaginary families.** For even `r`, `M = 2r` and `a = 1 + r`: if `8 ∤ r` then
--   `β(2r, 1 + r, s) = 0` for every `s`, and `β(2r, 1 + r, r/d) = 0` whenever `d ∣ r` is odd.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L221-L224
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L221-L224

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sqrtCount_imaginary {r : ℕ} (hr : 0 < r) (hev : Even r) :
    (¬ 8 ∣ r → ∀ s, sqrtCount (2 * r) (1 + r) s = 0) ∧
      (∀ d, d ∣ r → ¬ 2 ∣ d → sqrtCount (2 * r) (1 + r) (r / d) = 0) := by sorry
