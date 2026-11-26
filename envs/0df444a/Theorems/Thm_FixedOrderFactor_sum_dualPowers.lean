-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_dualPowers
-- name    : FixedOrderFactor.sum_dualPowers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:07.42625+00:00
-- url     : https://prove2.me/theorems/7d2c16d5-7660-46a5-ad08-0127cc535147
-- title:
--   Fixed Order Factor: sum dual Powers
-- statement:
--   Orthogonality over the characters trivial on the `r`-th powers.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L48-L71
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L48-L71

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]

theorem FixedOrderFactor.sum_dualPowers (r : ℕ) (u : (ZMod p)ˣ) :
    ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u =
      if u ∈ powers p r then (Nat.card (dualPowers p r) : ℂ) else 0 := by sorry
