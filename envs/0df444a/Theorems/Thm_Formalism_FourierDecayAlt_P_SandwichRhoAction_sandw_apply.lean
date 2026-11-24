-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_sandw_apply
-- name    : Formalism.FourierDecayAlt.P.SandwichRhoAction.sandw_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:39.428472+00:00
-- url     : https://prove2.me/theorems/8b2ae66a-5b56-4dd6-a6ab-e83e3613bd98
-- title:
--   Sandwich Rho Action: sandw apply
-- statement:
--   The Sandwich Rho Action construction uses the sandw apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L33-L33

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

theorem Formalism.FourierDecayAlt.P.SandwichRhoAction.sandw_apply (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (A : Wq →L[ℂ] Wp) : sandw P Q A = P.comp (A.comp Q) := by sorry
