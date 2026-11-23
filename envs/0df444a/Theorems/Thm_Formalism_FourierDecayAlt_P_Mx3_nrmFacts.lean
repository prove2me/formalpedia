-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrmFacts
-- name    : Formalism.FourierDecayAlt.P.Mx3.nrmFacts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:14.417012+00:00
-- url     : https://prove2.me/theorems/3c1a3d63-35b1-47fd-9e59-c6f9be65d3cd
-- title:
--   Mx3: nrm Facts
-- statement:
--   The Mx3 construction uses the nrm Facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L248-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L248-L267

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3

theorem Formalism.FourierDecayAlt.P.Mx3.nrmFacts : NrmFacts := by sorry
