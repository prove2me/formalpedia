-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_tuo_of_bound
-- name    : Formalism.FourierDecayAlt.P.Ux1.tuo_of_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:10:41.533802+00:00
-- url     : https://prove2.me/theorems/89062975-82bb-4712-8fac-dd1f388f0c84
-- title:
--   Ux1: tuo of bound
-- statement:
--   The Ux1 construction uses the tuo of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L512-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L512-L527

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Ux1.tuo_of_bound {α F : Type*} [NormedAddCommGroup F] {G : ℕ → α → F} {f : α → F} {s : Set α} {B : ℝ}
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∀ x ∈ s, ‖G n x - f x‖ ≤ B * ε n) :
    TendstoUniformlyOn G f atTop s := by sorry
