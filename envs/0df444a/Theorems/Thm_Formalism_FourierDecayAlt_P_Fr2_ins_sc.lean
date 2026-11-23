-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_ins_sc
-- name    : Formalism.FourierDecayAlt.P.Fr2.ins_sc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:36.428592+00:00
-- url     : https://prove2.me/theorems/c3eb66d1-45c6-4467-a50c-0c790e35aff4
-- title:
--   Fr2: ins sc
-- statement:
--   The Fr2 construction uses the ins sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L282-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L282-L290

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr2.ins_sc (a : S) (φ : ℂ) :
    (ins a !![φ • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] : SlopeTestRemainingChoices S A) =
      Matrix.diagonal (fun e => if e a = 0 then algebraMap ℂ A φ else 1) := by sorry
