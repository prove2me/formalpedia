-- Prove2me | Theorems.Thm_BooleanIsoperimetry_compress_VU_eq_blockReplace
-- name    : BooleanIsoperimetry.compress_VU_eq_blockReplace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:52.668104+00:00
-- url     : https://prove2.me/theorems/3185d469-d65d-4c30-a1df-1f52853388d9
-- title:
--   Boolean Isoperimetry: compress VU eq block Replace
-- statement:
--   **Per-set block dictionary.**  For disjoint blocks `U`, `V` the mathlib
--   single-element compression `UV.compress V U` agrees with the project's block
--   replacement: it is `blockReplace U V S = (S \ U) ∪ V` exactly when `U ⊆ S` and `V`
--   is disjoint from `S`, and the identity otherwise.  (Disjointness of `U`, `V` is
--   what makes `(S ∪ V) \ U = (S \ U) ∪ V`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L758-L765
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L758-L765

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

theorem BooleanIsoperimetry.compress_VU_eq_blockReplace {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (S : Cube N) :
    UV.compress V U S = (if U ⊆ S ∧ Disjoint V S then blockReplace U V S else S) := by sorry
