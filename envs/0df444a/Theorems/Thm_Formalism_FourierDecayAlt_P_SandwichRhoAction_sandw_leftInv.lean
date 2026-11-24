-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_sandw_leftInv
-- name    : Formalism.FourierDecayAlt.P.SandwichRhoAction.sandw_leftInv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:11.652234+00:00
-- url     : https://prove2.me/theorems/ef752f73-34c5-460b-b288-1f0df6966753
-- title:
--   Sandwich Rho Action: sandw left Inv
-- statement:
--   The Sandwich Rho Action construction uses the sandw left Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L38-L54

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.SandwichRhoAction.sandw_leftInv (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (A : Wq →L[ℂ] Wp) :
    sandw (D.π (Matrix.of p.1.1)⁻¹) (D.π' (Matrix.of p.2.1))
      (sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) A) = A := by sorry
