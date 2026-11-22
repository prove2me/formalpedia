-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_positionAfter
-- name    : Formalism.FourierDecayAlt.P.positionAfter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:23.321157+00:00
-- url     : https://prove2.me/theorems/6670104d-84e8-4522-ae52-05c75a0129dd
-- title:
--   P: position After
-- statement:
--   The P construction uses the position After property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L343-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L343-L375

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

theorem Formalism.FourierDecayAlt.P.positionAfter : PositionAfter := by sorry
