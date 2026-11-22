-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_one_eq_self_union_shadow_upShadow
-- name    : BooleanIsoperimetry.neighborhood_one_eq_self_union_shadow_upShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:49.422822+00:00
-- url     : https://prove2.me/theorems/764d5093-2c50-40a3-8984-6e2f28819810
-- title:
--   Boolean Isoperimetry: neighborhood one eq self union shadow up Shadow
-- statement:
--   **Closed unit neighborhood as the union of the family, its lower shadow, and
--   its upper shadow.**  In the Boolean cube the closed Hamming ball of radius 1 of a
--   family `A` is exactly `A ∪ ∂A ∪ ∂⁺A`: a vertex at Hamming distance `≤ 1` of some
--   `u ∈ A` is either `u` itself, a one-element subset (lower shadow `∂A`), or a
--   one-element superset (upper shadow `∂⁺A`).  This is the structural dictionary
--   bridging the project's metric `neighborhood 1` to mathlib's `Finset.shadow` /
--   `Finset.upShadow`, so the closed-neighborhood leaf below can be analysed with the
--   standard set-family shadow operators (and the already-proved UV shadow bounds).
--   Sorry-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L916-L976
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L916-L976

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

theorem BooleanIsoperimetry.neighborhood_one_eq_self_union_shadow_upShadow {N : ℕ} (A : Finset (Cube N)) :
    neighborhood 1 A = A ∪ Finset.shadow A ∪ Finset.upShadow A := by sorry
