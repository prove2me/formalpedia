-- Prove2me | Theorems.Thm_BooleanIsoperimetry_exists_lowerSatDownFixed_le_aux
-- name    : BooleanIsoperimetry.exists_lowerSatDownFixed_le_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:38.658874+00:00
-- url     : https://prove2.me/theorems/2d76347e-3acf-4f53-87ce-0d25a671c511
-- title:
--   Boolean Isoperimetry: exists lower Sat Down Fixed le aux
-- statement:
--   Well-founded descent (strong induction on potential) to a lower-saturated,
--   Down-fixed family, using only coordinate-Down and level-block moves.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2153-L2166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2153-L2166

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

theorem BooleanIsoperimetry.exists_lowerSatDownFixed_le_aux {N : ℕ} :
    ∀ n (A : Finset (Cube N)), compressionPotential A = n →
      ∃ A₁ : Finset (Cube N), IsCoordinateDownFixed A₁ ∧ IsLowerLevelSaturated A₁ ∧
        A₁.card = A.card ∧ (neighborhood 1 A₁).card ≤ (neighborhood 1 A).card := by sorry
