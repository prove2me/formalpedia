-- Prove2me | Theorems.Thm_Erdos1219_erdosRado_unbalanced_wo
-- name    : Erdos1219.erdosRado_unbalanced_wo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:44:03.167102+00:00
-- url     : https://prove2.me/theorems/7d25bdd9-8adb-4262-81d3-192d3138df93
-- title:
--   Erdos1219: erdos Rado unbalanced wo
-- statement:
--   The theorem on a well-ordered type of cardinality `(2^μ)⁺` and order type `(2^μ)⁺.ord`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L277-L287
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L277-L287

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]

theorem Erdos1219.erdosRado_unbalanced_wo {f : W → W → Bool} (hf : ∀ x y, f x y = f y x)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (c : Bool) :
    (∃ H : Set W, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H) := by sorry
