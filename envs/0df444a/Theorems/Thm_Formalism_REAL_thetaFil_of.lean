-- Prove2me | Theorems.Thm_Formalism_REAL_thetaFil_of
-- name    : Formalism.REAL.thetaFil_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:26:00.374635+00:00
-- url     : https://prove2.me/theorems/cb98a79e-e758-466f-bc02-41da53192517
-- title:
--   REAL: theta Fil of
-- statement:
--   The REAL construction uses the theta Fil of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L724-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L724-L727

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
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

theorem Formalism.REAL.thetaFil_of (hp : PfilFacts) : ThetaFil := by sorry
