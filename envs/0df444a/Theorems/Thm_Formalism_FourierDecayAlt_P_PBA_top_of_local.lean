-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_top_of_local
-- name    : Formalism.FourierDecayAlt.P.PBA.top_of_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:39.020649+00:00
-- url     : https://prove2.me/theorems/40cb9d41-95e0-40b8-b829-7a174cb8a840
-- title:
--   PBA: top of local
-- statement:
--   The PBA construction uses the top of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopOfLocal.lean#L12-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopOfLocal.lean#L12-L98

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section

theorem Formalism.FourierDecayAlt.P.PBA.top_of_local : KB.TopOfLoc := by sorry
