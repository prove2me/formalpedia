-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D3_hk
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.hk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:42.783798+00:00
-- url     : https://prove2.me/theorems/2060fde0-6312-4245-91d3-f2eff7b9fffc
-- title:
--   D3: hk
-- statement:
--   The D3 construction uses the hk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L741-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L741-L743

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.hk {c t m5 f : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (ht : t ≤ m5) : c * (f * t) ≤ c * (m5 * f) := by sorry
