-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_ubl_phiR
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.ubl_phiR
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:49.415742+00:00
-- url     : https://prove2.me/theorems/54387e38-dbf0-5339-afa7-dc1e0b048f33
-- title:
--   JA: ubl phi R
-- statement:
--   The JA construction uses the ubl phi R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScalBound.lean#L120-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScalBound.lean#L120-L134

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.ubl_phiR (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiR k r D.z D.z') (regE D ε) n r (r + 1) := by sorry
