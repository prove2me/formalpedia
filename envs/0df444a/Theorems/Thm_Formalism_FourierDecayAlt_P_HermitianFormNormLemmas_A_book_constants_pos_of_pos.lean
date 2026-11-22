-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_A_book_constants_pos_of_pos
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.book_constants_pos_of_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:10.676165+00:00
-- url     : https://prove2.me/theorems/1c6ebc90-46e7-4fcb-a523-3dac45fa1101
-- title:
--   A: book constants pos of pos
-- statement:
--   The A construction uses the book constants pos of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L13-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L13-L49

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.book_constants_pos_of_pos {P : Type} [Fintype P] (B : S3.MassData P) (h : B.Pos) :
    0 < B.Gam1 ∧ 0 < B.μK ∧ 0 < B.μKpp ∧ 0 < B.μSpp ∧ 0 < B.μSpp' ∧ 0 < B.MM ∧ 0 < B.unitLevelVolume ∧
    0 < B.c0 ∧ 0 < B.c0' ∧ 0 < B.tt ∧ 0 < B.AA ∧ 0 < B.Dstar := by sorry
