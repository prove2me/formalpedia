-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_zfns_comm
-- name    : Formalism.FourierDecayAlt.P.Fr7.zfns_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:42.669828+00:00
-- url     : https://prove2.me/theorems/5ae72ecb-630c-4225-8f8a-f27c93a5f39b
-- title:
--   Fr7: zfns comm
-- statement:
--   The Fr7 construction uses the zfns comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L198-L199

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr7.zfns_comm (L : LevelData A r) {g h : A} (hg : g ∈ zfns L) (hh : h ∈ zfns L) : g * h = h * g := by sorry
