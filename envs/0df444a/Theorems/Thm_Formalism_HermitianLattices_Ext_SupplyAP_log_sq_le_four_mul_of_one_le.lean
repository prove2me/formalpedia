-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_log_sq_le_four_mul_of_one_le
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.log_sq_le_four_mul_of_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:42.137832+00:00
-- url     : https://prove2.me/theorems/8d281c2f-36be-432a-9d8b-e830d9e0de71
-- title:
--   Supply AP: log sq le four mul of one le
-- statement:
--   The Supply AP construction uses the log sq le four mul of one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffExc.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffExc.lean#L10-L20

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_LfunctionOneLowerBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.log_sq_le_four_mul_of_one_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by sorry
