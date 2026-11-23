-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_TT_eq
-- name    : Formalism.FourierDecayAlt.P.Mx7.TT_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:41.567558+00:00
-- url     : https://prove2.me/theorems/924c0b65-a157-46fd-90c8-648e0d183e2b
-- title:
--   Mx7: TT eq
-- statement:
--   The Mx7 construction uses the TT eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L175-L180

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem Formalism.FourierDecayAlt.P.Mx7.TT_eq (P : Par) (l j : ℕ) (f g f' : Ty P → ℂ) (h : kap P f * SS P j = SS P j * kap P f') :
    (SS P l * kap P f) * (SS P j * kap P g) = SS P l * SS P j * kap P (f' * g) := by sorry
