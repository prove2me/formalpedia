-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_site_mem
-- name    : Formalism.FourierDecayAlt.P.Mx9.site_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:16.080864+00:00
-- url     : https://prove2.me/theorems/c2ec1be4-8847-451a-95da-d1aab1450a1a
-- title:
--   Mx9: site mem
-- statement:
--   The Mx9 construction uses the site mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L45-L46

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9

theorem Formalism.FourierDecayAlt.P.Mx9.site_mem (P : Par) (i : Fin P.r) : siteA P i ∈ sitesFrom P 0 := by sorry
