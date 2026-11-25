-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_jABddOpQQ_of_bddLeaves
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.jABddOpQQ_of_bddLeaves
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:32.673341+00:00
-- url     : https://prove2.me/theorems/2c3a672a-66a9-5770-8a3f-cd9271f1ee34
-- title:
--   JA: j ABdd Op QQ of bdd Leaves
-- statement:
--   The JA construction uses the j ABdd Op QQ of bdd Leaves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddOp.lean#L138-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddOp.lean#L138-L155

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.jABddOpQQ_of_bddLeaves (h1 : JABddScal) (h2 : JABddKapQQ) (h3 : JABddSSnQQ) (h4 : JABddSSnStarQQ) :
    JABddOpQQ := by sorry
