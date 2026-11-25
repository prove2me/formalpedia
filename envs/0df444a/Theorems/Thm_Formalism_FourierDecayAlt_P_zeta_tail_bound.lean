-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_zeta_tail_bound
-- name    : Formalism.FourierDecayAlt.P.zeta_tail_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:35:34.051132+00:00
-- url     : https://prove2.me/theorems/4b30b6a9-b3a7-53a3-94d5-73f03f5ef15c
-- title:
--   P: zeta tail bound
-- statement:
--   The P construction uses the zeta tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L445-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L445-L445

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.zeta_tail_bound : Formalism.FourierDecayAlt.Sz.ZetaTail := by sorry
