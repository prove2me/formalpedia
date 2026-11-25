-- Prove2me | Theorems.Thm_Formalism_L2_Indef_ColData_pairing_iff_inverse_matrix_identity
-- name    : Formalism.L2.Indef.ColData.pairing_iff_inverse_matrix_identity
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:14.437853+00:00
-- url     : https://prove2.me/theorems/9606b3bd-955c-54bd-ab14-dbac778036e4
-- title:
--   Col Data: pairing iff inverse matrix identity
-- statement:
--   The Col Data construction uses the pairing iff inverse matrix identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L69-L70

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

theorem Formalism.L2.Indef.ColData.pairing_iff_inverse_matrix_identity (h0 : S.H0) : C.PairingFactorsThroughPeriods ↔ C.invZ.MatrixIdentityOffBase := by sorry
