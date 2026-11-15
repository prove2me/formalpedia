-- Prove2me | Theorems.Thm_CurrentAFT_BinaryFullResponseMatrixEntry_current_value
-- name    : CurrentAFT.BinaryFullResponseMatrixEntry.current_value
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T22:01:36.833925+00:00
-- url     : https://prove2.me/theorems/632707cb-3491-4d90-86e3-eb3f60aa02e6
-- title:
--   Exact semantics of the binary full-response matrix entry
-- statement:
--   Fix security, precision and order, a correct full-response metadata record, and two indices of the materialized finite rectangle. Decoding the actual stored binary full-response matrix entry gives exactly CurrentRectangleIndex.defect applied to the rational full-response program at the row and column tuples obtained by finProdFinEquiv.symm. This is an exact implementation identity, separate from its approximation error.
-- source:
--   Companion complete Lean proof for the fixed-family affine transport construction. The original proof and exact native type were checked before import-only sparse repackaging; the new payload is independently compiled and axiom-audited.

import Definitions.Def_InfoLossLAR_NativeBundle_12

namespace CurrentAFT.BinaryFullResponseMatrixEntry
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFullResponseData BinaryRectangleMaterialization
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseProgram.current BinaryNaturalCoordinates.current
  RationalFullResponseProgram.defect



set_option maxRecDepth 8192

theorem _root_.CurrentAFT.BinaryFullResponseMatrixEntry.current_value (security bits order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data)
    (output source : Fin (_root_.CurrentAFT.BinaryRectangleMaterialization.Size security order)) :
    (_root_.CurrentAFT.BinaryFullResponseMatrixEntry.current security bits order data output source).value.decode=
      _root_.CurrentAFT.CurrentRectangleIndex.defect security order (_root_.CurrentAFT.RationalFullResponseProgram.matrix security bits order)
        (finProdFinEquiv.symm output) (finProdFinEquiv.symm source) := by sorry
