-- Prove2me | Theorems.Thm_BooleanIsoperimetry_minDelta_pair_admissible_dual_A
-- name    : BooleanIsoperimetry.minDelta_pair_admissible_dual_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:26.795918+00:00
-- url     : https://prove2.me/theorems/4d227ed3-1eae-43d9-b8d6-5297c8928a56
-- title:
--   Boolean Isoperimetry: min Delta pair admissible dual A
-- statement:
--   The Boolean Isoperimetry construction uses the min Delta pair admissible dual A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1707-L1789
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1707-L1789

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

theorem BooleanIsoperimetry.minDelta_pair_admissible_dual_A {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((S \ T).erase x) ((T \ S).erase y) A = A := by sorry
