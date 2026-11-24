-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_dw_integrable
-- name    : Formalism.FourierDecayAlt.P.PBB.K8.dw_integrable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:10.881788+00:00
-- url     : https://prove2.me/theorems/32a0fcaa-fb13-46f4-878d-e7a3a7b2b634
-- title:
--   K8: dw integrable
-- statement:
--   The K8 construction uses the dw integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramLocTendsto.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramLocTendsto.lean#L18-L24

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section

theorem Formalism.FourierDecayAlt.P.PBB.K8.dw_integrable : Integrable dw := by sorry
