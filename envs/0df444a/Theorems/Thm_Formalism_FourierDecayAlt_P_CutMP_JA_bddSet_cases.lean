-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_bddSet_cases
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.bddSet_cases
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:23:37.429456+00:00
-- url     : https://prove2.me/theorems/9a8f71d4-efda-5c41-9177-ee334f72d513
-- title:
--   JA: bdd Set cases
-- statement:
--   The JA construction uses the bdd Set cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddOp.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddOp.lean#L60-L68

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
open NumberField Formalism.FourierDecayAlt.P.CutMP
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.JA.bddSet_cases (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (b : MA.A P (MA.DQ P))
    (hb : b ∈ MA.bddSet P L) :
    b ∈ scalSet P L ∨ b ∈ Set.range (MA.kap P (MA.DQ P)) ∨ b ∈ ssnSet P L ∨ b ∈ ssnStarSet P L := by sorry
