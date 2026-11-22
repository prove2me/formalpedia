-- Prove2me | Theorems.Thm_Formalism_L2_Indef_ColData_invZ_B
-- name    : Formalism.L2.Indef.ColData.invZ_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:42.746356+00:00
-- url     : https://prove2.me/theorems/ce1f2cb9-b9d2-47ac-80b9-7c40091eafce
-- title:
--   Col Data: inv Z B
-- statement:
--   The Col Data construction uses the inv Z B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L29-L29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)

theorem Formalism.L2.Indef.ColData.invZ_B : C.invZ.B = C.B := by sorry

attribute [defeq] Formalism.L2.Indef.ColData.invZ_B
