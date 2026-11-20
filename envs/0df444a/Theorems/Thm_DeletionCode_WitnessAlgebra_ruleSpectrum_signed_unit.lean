-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_ruleSpectrum_signed_unit
-- name    : DeletionCode.WitnessAlgebra.ruleSpectrum_signed_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:27.007162+00:00
-- url     : https://prove2.me/theorems/638b34f5-2d2c-4add-bac1-a11313129b3f
-- title:
--   Witness Algebra: rule Spectrum signed unit
-- statement:
--   Catalogue geometry gives the signed-unit premise for actual rule spectra.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L22-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L22-L43

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.ruleSpectrum_signed_unit {B : Type*} (F : RootSelection.Family B) (L : ℕ)
    (H : SignedSupport.BubbleGeometry F L) (S : Finset B)
    (hdis : SignedSupport.VertexDisjointOn F L S) :
    SignedUnitVector (fun g => (SignedSupport.ruleSpectrum F L S g : ℚ)) := by sorry
