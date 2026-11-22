-- Prove2me | Theorems.Thm_BooleanIsoperimetry_minDelta_pair_admissible_primal
-- name    : BooleanIsoperimetry.minDelta_pair_admissible_primal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:23.983155+00:00
-- url     : https://prove2.me/theorems/c8a770cb-3782-48e8-9378-35e930f12e19
-- title:
--   Boolean Isoperimetry: min Delta pair admissible primal
-- statement:
--   **Primal directional leaf.**  The lower-shadow (primal) erase-admissibility
--   clause for the minimal-symmetric-difference extremal pair.  For each `x` in the
--   inserted block `T \ S` some coordinate `y` of the removed block `S \ T` can be
--   spared so that the trimmed level-block move `familyUp ((S\T).erase y)
--   ((T\S).erase x) A` fixes `A` setwise.  Proved (or to be proved) via the trivial-move
--   characterization `familyUp_eq_self_iff` and a contradiction against the
--   symmetric-difference minimality `hmin`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1622-L1705
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1622-L1705

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

theorem BooleanIsoperimetry.minDelta_pair_admissible_primal {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (_ : IsCoordinateDownFixed A)
    (_ : T ∉ A)
    (_ : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A := by sorry
