-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_jdh_SSn_mem
-- name    : Formalism.FourierDecayAlt.P.CutMP.jdh_SSn_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:31:36.997698+00:00
-- url     : https://prove2.me/theorems/c6eb197e-75ac-5bf3-bf23-69a57b48cf16
-- title:
--   Cut MP: jdh SSn mem
-- statement:
--   The Cut MP construction uses the jdh SSn mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHat.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHat.lean#L162-L164

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
variable (P : M.Par)

theorem Formalism.FourierDecayAlt.P.CutMP.jdh_SSn_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    SSn P L l ∈ Submonoid.closure (MA.bddSet P L) := by sorry
