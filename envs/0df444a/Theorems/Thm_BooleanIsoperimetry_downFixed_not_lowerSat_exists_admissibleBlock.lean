-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downFixed_not_lowerSat_exists_admissibleBlock
-- name    : BooleanIsoperimetry.downFixed_not_lowerSat_exists_admissibleBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:25.017799+00:00
-- url     : https://prove2.me/theorems/b44e4f76-24e9-4709-af9d-23bbad347709
-- title:
--   Boolean Isoperimetry: down Fixed not lower Sat exists admissible Block
-- statement:
--   The Boolean Isoperimetry construction uses the down Fixed not lower Sat exists admissible Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1822-L1831
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1822-L1831

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

theorem BooleanIsoperimetry.downFixed_not_lowerSat_exists_admissibleBlock {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card ∧
    (∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A) ∧
    (∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ) := by sorry
