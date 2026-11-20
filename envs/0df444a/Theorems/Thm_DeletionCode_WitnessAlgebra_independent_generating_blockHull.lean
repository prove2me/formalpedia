-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_independent_generating_blockHull
-- name    : DeletionCode.WitnessAlgebra.independent_generating_blockHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:06.814408+00:00
-- url     : https://prove2.me/theorems/66c71694-95c7-4b66-bc20-bc5375645ead
-- title:
--   Witness Algebra: independent generating block Hull
-- statement:
--   Whole-block retention preserves independence as well as signed generation.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L46-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L46-L56

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.independent_generating_blockHull {I : Type*} {L : ℕ}
    (v : SignedSupport.Gram L → ℤ) (G : I → SignedSupport.Gram L → ℤ)
    (rank : I → ℕ) (T : Set I) (hgen : GeneratingBlocks.Generating v G rank)
    (hind : LinearIndependent ℚ (fun i h => (G i h : ℚ))) :
    GeneratingBlocks.Generating v
      (fun i : GeneratingBlocks.blockHull G T => G i.val)
      (fun i : GeneratingBlocks.blockHull G T => rank i.val) ∧
    LinearIndependent ℚ
      (fun (i : GeneratingBlocks.blockHull G T) h => (G i.val h : ℚ)) := by sorry
