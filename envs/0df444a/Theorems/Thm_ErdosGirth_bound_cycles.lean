-- Prove2me | Theorems.Thm_ErdosGirth_bound_cycles
-- name    : ErdosGirth.bound_cycles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:49.090862+00:00
-- url     : https://prove2.me/theorems/f3175d97-1ca9-5b62-8cb9-667375341c86
-- title:
--   Erdos Girth: bound cycles
-- statement:
--   The Erdos Girth construction uses the bound cycles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L371-L407
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L371-L407

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.bound_cycles (g q : ℕ) (hq : 4 * (g + 1) * (2 ^ (2 * g + 3)) ^ g < q) (m : ℝ)
    (hm1 : (q : ℝ) ^ (2 * g + 3) ≤ m) (hm2 : m ≤ ((q : ℝ) + 1) ^ (2 * g + 3)) :
    2 / m * ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ < 1 / 2 := by sorry
