-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_ubl_phiD
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.ubl_phiD
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:11.268287+00:00
-- url     : https://prove2.me/theorems/b7239b05-003d-5227-94a9-e72063b19f8a
-- title:
--   JA: ubl phi D
-- statement:
--   The JA construction uses the ubl phi D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScalBound.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScalBound.lean#L136-L150

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScalBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
noncomputable section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.CutMP.JA.ubl_phiD (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiD k r D.z D.z') (regE D ε) n (r + 1) (r + 1) := by sorry
