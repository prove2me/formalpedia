-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_scalar_partial_fraction_identity
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.scalar_partial_fraction_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:07.065459+00:00
-- url     : https://prove2.me/theorems/3e1ce901-3684-4594-b87a-7e61da487265
-- title:
--   WB: scalar partial fraction identity
-- statement:
--   The WB construction uses the scalar partial fraction identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L781-L801
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L781-L801

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx6.WB.scalar_partial_fraction_identity (P : Par) (hP : P.OK) (π : Ty P) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) * ((u + v + 1 + 2 * (aC P π : ℂ)) * (P.TT : ℂ) + ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))) =
      qC P v / (xC P π v * xC P π (v + 1)) - qC P u / (xC P π u * xC P π (u + 1)) := by sorry
