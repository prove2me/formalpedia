-- Prove2me | Theorems.Thm_Erdos1219_erdosRado_unbalanced
-- name    : Erdos1219.erdosRado_unbalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:44:06.575071+00:00
-- url     : https://prove2.me/theorems/be3a1d36-fb95-4b8a-934d-49ba2ed9e26b
-- title:
--   Erdos1219: erdos Rado unbalanced
-- statement:
--   The unbalanced Erdős–Rado theorem `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²`, stated for both colours `c`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L294-L322
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L294-L322

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u

theorem Erdos1219.erdosRado_unbalanced {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (C : Set V) (hC : #C = Order.succ (2 ^ μ)) (c : Bool) :
    (∃ H ⊆ C, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H ⊆ C, #H = Order.succ μ ∧ Homog f (!c) H) := by sorry
