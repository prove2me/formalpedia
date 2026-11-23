-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_nab_SSs
-- name    : Formalism.FourierDecayAlt.P.Mx7.nab_SSs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:41.275423+00:00
-- url     : https://prove2.me/theorems/0349329b-ef90-4c6a-993e-937fd7c9f0b8
-- title:
--   Mx7: nab SSs
-- statement:
--   The Mx7 construction uses the nab SSs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1263-L1276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1263-L1276

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

theorem Formalism.FourierDecayAlt.P.Mx7.nab_SSs (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    nabA P * star (SS P l) = star (SS P l) * nabA P + zbA P * ggiA P * star (SS P l) := by sorry
