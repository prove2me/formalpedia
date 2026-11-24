-- Prove2me | Theorems.Thm_Formalism_REAL_typesSplit_of
-- name    : Formalism.REAL.typesSplit_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:56.93773+00:00
-- url     : https://prove2.me/theorems/50b567f9-1f0e-4c5c-aefd-29f05ec16965
-- title:
--   REAL: types Split of
-- statement:
--   The REAL construction uses the types Split of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L285-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L285-L316

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.typesSplit_of (hv : HVCoeff) (hi : KIsoSplit) (ha : ArrModule) : TypesSplit := by sorry
