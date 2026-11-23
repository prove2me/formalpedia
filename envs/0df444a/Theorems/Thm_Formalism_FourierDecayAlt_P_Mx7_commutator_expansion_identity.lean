-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_commutator_expansion_identity
-- name    : Formalism.FourierDecayAlt.P.Mx7.commutator_expansion_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:08.419294+00:00
-- url     : https://prove2.me/theorems/3a339d09-7306-4eea-b01b-f48d62ca9cf3
-- title:
--   Mx7: commutator expansion identity
-- statement:
--   The Mx7 construction uses the commutator expansion identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1045-L1053
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1045-L1053

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
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem Formalism.FourierDecayAlt.P.Mx7.commutator_expansion_identity (a ap am S Ss Nn Nd : R) (h1 : Ss * a = ap * Ss) (h2 : S * a = am * S) (hn : Ss * S = Nn)
    (hd : S * Ss = Nd) : a * Ss * (a * S) - a * S * (a * Ss) = a * ap * Nn - a * am * Nd := by sorry
