-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downFixed_downClosed
-- name    : BooleanIsoperimetry.downFixed_downClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:55.821806+00:00
-- url     : https://prove2.me/theorems/059d364d-e90c-4f24-82d7-9a25c4307386
-- title:
--   Boolean Isoperimetry: down Fixed down Closed
-- statement:
--   **Existence of a paper level block from lower-level-saturation failure.**
--
--   For a coordinate-Down-fixed family `A` that is not lower-level-saturated, there is
--   a present block `U ∈ A` with `2 ≤ U.card` and a coordinate `j ∉ U` such that the
--   single-coordinate level move `familyUp U {j} A` is nontrivial: some `S ∈ A`
--   containing `U` and avoiding `j` has its block replacement `(S \ U) ∪ {j}` outside
--   `A`.
--
--   This is the genuine combinatorial core (a strictly smaller terminalization
--   lemma): the admissibility of the resulting move is automatic from down-fixedness
--   (`downFixed_familyUp_erase_eq`, `downFixed_familyUp_add_compls_eq`), so only this
--   pure existence statement remains.  It is finite-checked NO_COUNTEREXAMPLE for
--   `N ≤ 4` by `verify_paperBlock_existence_small.py` (clean-form column).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1382-L1392
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1382-L1392

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

theorem BooleanIsoperimetry.downFixed_downClosed {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {R S : Cube N} (hS : S ∈ A) (hRS : R ⊆ S) :
    R ∈ A := by sorry
