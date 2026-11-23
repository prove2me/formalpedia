-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_normsq_tsum
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.normsq_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:42.322606+00:00
-- url     : https://prove2.me/theorems/9b56ec29-a637-4a0d-92c6-f98707a0c4fc
-- title:
--   C: normsq tsum
-- statement:
--   The C construction uses the normsq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L480-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L480-L503

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
variable {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.normsq_tsum (a : ι → V) (ha : Summable (fun i => ‖a i‖)) :
    ‖∑' i, a i‖ ^ 2 = ∑' p : ι × ι, (inner ℂ (a p.1) (a p.2) : ℂ).re := by sorry
