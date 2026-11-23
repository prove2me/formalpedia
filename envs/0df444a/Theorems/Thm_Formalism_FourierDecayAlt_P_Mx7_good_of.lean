-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_good_of
-- name    : Formalism.FourierDecayAlt.P.Mx7.good_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:26.331373+00:00
-- url     : https://prove2.me/theorems/a7a2c51d-65b2-46d0-b1ec-fff345c1d026
-- title:
--   Mx7: good of
-- statement:
--   The Mx7 construction uses the good of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1480-L1491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1480-L1491

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial

theorem Formalism.FourierDecayAlt.P.Mx7.good_of (P : Par) (Y : ℂ) (hY : Y ∉ badSet P) (c : ℂ) (hc : c = 0 ∨ c = 1 ∨ c = 2) (π : Ty P) :
    xC P π (Y + c) ≠ 0 := by sorry
