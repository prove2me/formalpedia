-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerInitSeg_compls_isInitSeg
-- name    : BooleanIsoperimetry.layerInitSeg_compls_isInitSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:20.31643+00:00
-- url     : https://prove2.me/theorems/378ad1c4-1dd2-43ca-929c-358e20c3c165
-- title:
--   Boolean Isoperimetry: layer Init Seg compls is Init Seg
-- statement:
--   The complement of a simplicial layer initial segment is a colex initial
--   segment.  This is the remaining order-orientation bridge needed to feed the
--   project's layer initial segments into mathlib's lower-shadow Kruskal--Katona
--   theorem.
--
--   On a fixed Hamming layer, the project order takes larger binary/colex values
--   first; complementation changes a larger `r`-set value into a smaller
--   `(N-r)`-set value.  Thus complements of project initial segments are ordinary
--   colex initial segments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L419-L453
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L419-L453

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry

theorem BooleanIsoperimetry.layerInitSeg_compls_isInitSeg {N r t : ℕ} (_ : t ≤ Nat.choose N r) :
    Finset.Colex.IsInitSeg (layerInitSeg N r t)ᶜˢ (N - r) := by sorry
