-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_pow_card_eq
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.pow_card_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:58.344915+00:00
-- url     : https://prove2.me/theorems/fc8a8bd5-16f0-4292-970b-396a9c6d01b5
-- title:
--   B: pow card eq
-- statement:
--   The B construction uses the pow card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L251-L253

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

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.pow_card_eq {P : Type} [Fintype P] (Om : Finset P) (a : ℝ) :
    a ^ Om.card = ∏ p, if p ∈ Om then a else 1 := by sorry
