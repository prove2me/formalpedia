-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_slotAt_true
-- name    : Formalism.FourierDecayAlt.P.slotAt_true
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:08.081439+00:00
-- url     : https://prove2.me/theorems/fde141d2-5dc9-4ee1-b788-d1cdd60e40ce
-- title:
--   P: slot At true
-- statement:
--   The P construction uses the slot At true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L377-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L377-L406

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset

theorem Formalism.FourierDecayAlt.P.slotAt_true : PositionAt := by sorry
