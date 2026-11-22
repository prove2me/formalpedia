-- Prove2me | Theorems.Thm_BooleanIsoperimetry_minDelta_pair_admissible
-- name    : BooleanIsoperimetry.minDelta_pair_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:27.60868+00:00
-- url     : https://prove2.me/theorems/ed1b1c91-523b-4eb3-be02-0c3a9a6e1772
-- title:
--   Boolean Isoperimetry: min Delta pair admissible
-- statement:
--   The Boolean Isoperimetry construction uses the min Delta pair admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1810-L1820
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1810-L1820

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

theorem BooleanIsoperimetry.minDelta_pair_admissible {N : ℕ} {A : Finset (Cube N)} {T S : Cube N}
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    (∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A) ∧
    (∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ) := by sorry
