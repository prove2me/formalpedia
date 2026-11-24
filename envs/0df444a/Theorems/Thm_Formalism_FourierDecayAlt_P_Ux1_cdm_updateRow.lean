-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_updateRow
-- name    : Formalism.FourierDecayAlt.P.Ux1.cdm_updateRow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:10:50.834653+00:00
-- url     : https://prove2.me/theorems/65d6d41d-c5a5-4627-8a69-3c3d4fb4ee67
-- title:
--   Ux1: cdm update Row
-- statement:
--   The Ux1 construction uses the cdm update Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L116-L122

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}

theorem Formalism.FourierDecayAlt.P.Ux1.cdm_updateRow {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (j : Fin (2 * r + k + 1))
    (b : Fin (2 * r + k + 1) → ℂ) : ContDiffOn ℝ n (fun x => (F x).updateRow j b) s := by sorry
