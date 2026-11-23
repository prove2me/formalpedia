-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_per_l
-- name    : Formalism.FourierDecayAlt.P.Mx7.per_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:41.930039+00:00
-- url     : https://prove2.me/theorems/faa24a30-cc9a-4c3d-974f-9ca3c933e90e
-- title:
--   Mx7: per l
-- statement:
--   The Mx7 construction uses the per l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1307-L1337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1307-L1337

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

theorem Formalism.FourierDecayAlt.P.Mx7.per_l (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (hP : P.OK) (u : ℂ)
    (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ j ∈ Icc 1 (P.k - 1), kap P (bb P u l) * star (SS P l) * (kap P (bb P u j) * SS P j) -
      ∑ j ∈ Icc 1 (P.k - 1), kap P (bb P u j) * SS P j * (kap P (bb P u l) * star (SS P l)) =
    kap P fun π => (Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
      (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹) := by sorry
