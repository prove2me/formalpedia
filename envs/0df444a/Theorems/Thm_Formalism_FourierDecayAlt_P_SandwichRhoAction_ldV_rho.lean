-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_ldV_rho
-- name    : Formalism.FourierDecayAlt.P.SandwichRhoAction.ldV_rho
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:36.625798+00:00
-- url     : https://prove2.me/theorems/c257e13f-747f-49fd-8522-aedf4a827698
-- title:
--   Sandwich Rho Action: ld V rho
-- statement:
--   The Sandwich Rho Action construction uses the ld V rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L101-L105

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

theorem Formalism.FourierDecayAlt.P.SandwichRhoAction.ldV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (rho D p φ) g = rho D p (LdV (AdL p X) φ) g := by sorry
