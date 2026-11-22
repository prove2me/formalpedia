-- Prove2me | Theorems.Thm_BooleanIsoperimetry_embeddedPair_eq_of_slice_eq
-- name    : BooleanIsoperimetry.embeddedPair_eq_of_slice_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:38.383591+00:00
-- url     : https://prove2.me/theorems/c3ef30a4-1ae3-4fb2-8d6f-1bc44bdb5460
-- title:
--   Boolean Isoperimetry: embedded Pair eq of slice eq
-- statement:
--   The Boolean Isoperimetry construction uses the embedded Pair eq of slice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L120-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L120-L147

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.embeddedPair_eq_of_slice_eq {N : ℕ} {A : Finset (Cube (N + 1))} {P Q : Finset (Cube N)}
    (h0 : slice0 A = P) (h1 : slice1 A = Q) :
    A = embeddedPair N P Q := by sorry
