-- Prove2me | Theorems.Thm_Formalism_REAL_taylorSummable_holds
-- name    : Formalism.REAL.taylorSummable_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:53.343487+00:00
-- url     : https://prove2.me/theorems/624b367c-d595-43be-90ec-5a51aa3284cb
-- title:
--   REAL: taylor Summable holds
-- statement:
--   The REAL construction uses the taylor Summable holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuadraticInequalityBoundHolds.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuadraticInequalityBoundHolds.lean#L33-L47

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.taylorSummable_holds : TaylorRadius := by sorry
