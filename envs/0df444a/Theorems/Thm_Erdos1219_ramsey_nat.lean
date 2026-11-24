-- Prove2me | Theorems.Thm_Erdos1219_ramsey_nat
-- name    : Erdos1219.ramsey_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:56.817794+00:00
-- url     : https://prove2.me/theorems/6ed49c5f-86e9-4060-85f5-0015462663de
-- title:
--   Erdos1219: ramsey nat
-- statement:
--   Ramsey's theorem for pairs on `ℕ`: for every colouring `g` of ordered pairs `(p, q)` with
--   `p < q` (only those values matter), there is a strictly increasing sequence `m` and a colour `δ`
--   with `g (m p) (m q) = δ` whenever `p < q`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Ramsey.lean#L25-L95
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Ramsey.lean#L25-L95

import Definitions.Def_Erdos1219_Defs
import Mathlib.Order.Filter.Ultrafilter.Basic
import Definitions.Def_Erdos1219_Ramsey
set_option autoImplicit false
open Cardinal
open Erdos1219

theorem Erdos1219.ramsey_nat (g : ℕ → ℕ → Bool) :
    ∃ (m : ℕ → ℕ) (δ : Bool), StrictMono m ∧ ∀ p q, p < q → g (m p) (m q) = δ := by sorry
