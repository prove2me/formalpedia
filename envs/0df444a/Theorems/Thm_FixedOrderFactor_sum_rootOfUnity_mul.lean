-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_rootOfUnity_mul
-- name    : FixedOrderFactor.sum_rootOfUnity_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:45.927159+00:00
-- url     : https://prove2.me/theorems/026a73bc-c0f4-45cb-b053-2cfcc8c0f1f3
-- title:
--   Fixed Order Factor: sum root Of Unity mul
-- statement:
--   `∑_{t<s} e^{2πict/s}` is `s` if `s ∣ c` and `0` otherwise.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L44-L56
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L44-L56

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem FixedOrderFactor.sum_rootOfUnity_mul {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ range s, rootOfUnity s (c * t) = if s ∣ c then (s : ℂ) else 0 := by sorry
