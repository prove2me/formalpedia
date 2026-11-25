-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_bddClassOpQQ_of
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.bddClassOpQQ_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:22:18.470555+00:00
-- url     : https://prove2.me/theorems/998c8b83-47d6-4ab7-8888-6cc70f9088f3
-- title:
--   JA: bdd Class Op QQ of
-- statement:
--   The JA construction uses the bdd Class Op QQ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddOp.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddOp.lean#L126-L130

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.bddClassOpQQ_of (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P)))
    (h : BddClassOp cls) : BddClassOpQQ cls := by sorry
