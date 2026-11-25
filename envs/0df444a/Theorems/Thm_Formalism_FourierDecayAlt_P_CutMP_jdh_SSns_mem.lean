-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_jdh_SSns_mem
-- name    : Formalism.FourierDecayAlt.P.CutMP.jdh_SSns_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:33:25.478038+00:00
-- url     : https://prove2.me/theorems/55b9ef28-4f82-4df8-9a09-192396288657
-- title:
--   Cut MP: jdh SSns mem
-- statement:
--   The Cut MP construction uses the jdh SSns mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHat.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHat.lean#L166-L168

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

theorem Formalism.FourierDecayAlt.P.CutMP.jdh_SSns_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    star (SSn P L l) ∈ Submonoid.closure (MA.bddSet P L) := by sorry
