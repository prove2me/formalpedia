-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_finish
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.finish
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:32.471018+00:00
-- url     : https://prove2.me/theorems/380d456a-b5d5-4157-b4ed-6b281f6a0541
-- title:
--   B: finish
-- statement:
--   The B construction uses the finish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L255-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L255-L268

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.finish (L : LocalNG Cl Nu) (Xp Yp : L.P → ℝ) (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (e : ℕ)
    (h : ∀ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) ≤ L.H p ^ e) :
    (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) ≤ L.Htot ^ e := by sorry
