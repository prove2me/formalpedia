-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pf
-- name    : Formalism.FourierDecayAlt.P.Mx7.pf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:34:37.257597+00:00
-- url     : https://prove2.me/theorems/33f426d3-14ed-49b6-8ebd-e27b0b20e0c7
-- title:
--   Mx7: pf
-- statement:
--   The Mx7 construction uses the pf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L720-L767
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L720-L767

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
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx7.pf (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (h0 : xC P π (u - 1) ≠ 0) (h1 : xC P π u ≠ 0)
    (h2 : xC P π (u + 1) ≠ 0) :
    qC P (u - 1) * ((xC P π (u - 1))⁻¹ * (xC P π u)⁻¹) - qC P u * ((xC P π u)⁻¹ * (xC P π (u + 1))⁻¹) =
      (2 * (aC P π : ℂ) + 2 * u) * (P.TT : ℂ) + ∑ l ∈ Icc 1 (P.k - 1),
        ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by sorry
