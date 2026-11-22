-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_upperShadow_card_le_of_admissible
-- name    : BooleanIsoperimetry.familyUp_upperShadow_card_le_of_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:27.099822+00:00
-- url     : https://prove2.me/theorems/b4e49d17-bb4d-4243-ad09-e2ef62de383f
-- title:
--   Boolean Isoperimetry: family Up upper Shadow card le of admissible
-- statement:
--   **Block move does not increase the upper shadow** (the dual of
--   `familyUp_shadow_card_le_of_admissible`).  Phrased via the complement bijection
--   (`#(∂⁺ F) = #(∂ Fᶜˢ)`, mathlib `Finset.shadow_compls`): the lower shadow of the
--   complemented image is bounded by that of `Aᶜˢ`.  Needs the *dual* admissibility
--   `IsUVAdmissibleForFamily (Aᶜˢ) V U` of the complemented family for the swapped
--   blocks — admissibility of the lower-shadow move alone does **not** control the
--   upper shadow (a finite counterexample exists already at `N = 3`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L901-L905
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L901-L905

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

theorem BooleanIsoperimetry.familyUp_upperShadow_card_le_of_admissible {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    ((familyUp U V A)ᶜˢ).shadow.card ≤ (Aᶜˢ).shadow.card := by sorry
