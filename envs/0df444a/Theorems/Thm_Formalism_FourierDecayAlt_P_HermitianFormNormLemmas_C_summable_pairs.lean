-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_summable_pairs
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.summable_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:13.56237+00:00
-- url     : https://prove2.me/theorems/aa54dbfd-677d-48ac-a93c-5e8be13285b4
-- title:
--   C: summable pairs
-- statement:
--   The C construction uses the summable pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L470-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L470-L478

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

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.summable_pairs (a : ι → V) (ha : Summable (fun i => ‖a i‖)) :
    Summable (fun p : ι × ι => (inner ℂ (a p.1) (a p.2) : ℂ)) := by sorry
