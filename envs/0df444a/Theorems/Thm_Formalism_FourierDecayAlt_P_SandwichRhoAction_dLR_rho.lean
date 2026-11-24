-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_dLR_rho
-- name    : Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:08:09.231911+00:00
-- url     : https://prove2.me/theorems/76c2fe21-c873-4be3-ad19-d2fdb58f9140
-- title:
--   Sandwich Rho Action: d LR rho
-- statement:
--   The Sandwich Rho Action construction uses the d LR rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L124-L127

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

theorem Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (u v : List (Mat k r))
    (f : Mat k r → (Wq →L[ℂ] Wp)) : dLR u v (rho D p f) = rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) f) := by sorry
