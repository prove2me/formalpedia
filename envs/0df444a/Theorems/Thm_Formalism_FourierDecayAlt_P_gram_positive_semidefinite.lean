-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_gram_positive_semidefinite
-- name    : Formalism.FourierDecayAlt.P.gram_positive_semidefinite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:17.776801+00:00
-- url     : https://prove2.me/theorems/c7c22340-8b66-4b82-9d6f-f0496bb5f161
-- title:
--   P: gram positive semidefinite
-- statement:
--   The P construction uses the gram positive semidefinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelZeroEstimateProduct.lean#L27-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelZeroEstimateProduct.lean#L27-L62

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.gram_positive_semidefinite : C.GramPSDOfParts := by sorry
