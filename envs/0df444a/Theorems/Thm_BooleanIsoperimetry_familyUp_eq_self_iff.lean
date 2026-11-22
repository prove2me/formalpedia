-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_eq_self_iff
-- name    : BooleanIsoperimetry.familyUp_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:11.578893+00:00
-- url     : https://prove2.me/theorems/cdf8caf3-4898-4645-bdfe-5bd3052fde0e
-- title:
--   Boolean Isoperimetry: family Up eq self iff
-- statement:
--   **Characterization of a trivial `𝒰`-move (Mathlib dictionary lemma).**
--
--   The family `𝒰`-move `familyUp W₁ W₂ A` fixes `A` setwise exactly when no set of `A`
--   is actually moved: for every `R ∈ A` with `W₁ ⊆ R` and `W₂` disjoint from `R`, the
--   block replacement `blockReplace W₁ W₂ R = (R \ W₁) ∪ W₂` already lies in `A`.  This
--   is a pure image/injectivity dictionary fact about `familyUp = A.image (familyUpMap …)`
--   and the definitional guard of `familyUpMap`; it carries no combinatorial content and
--   is reused by both directional admissibility leaves.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1530-L1551
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1530-L1551

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

theorem BooleanIsoperimetry.familyUp_eq_self_iff {N : ℕ} (W₁ W₂ : Cube N) (A : Finset (Cube N)) :
    familyUp W₁ W₂ A = A ↔
      ∀ R ∈ A, W₁ ⊆ R → Disjoint W₂ R → blockReplace W₁ W₂ R ∈ A := by sorry
