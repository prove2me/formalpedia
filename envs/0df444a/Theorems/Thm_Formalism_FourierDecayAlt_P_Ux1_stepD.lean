-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_stepD
-- name    : Formalism.FourierDecayAlt.P.Ux1.stepD
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:10:34.283932+00:00
-- url     : https://prove2.me/theorems/614d21ea-003f-4fd5-b58f-5c693c927e97
-- title:
--   Ux1: step D
-- statement:
--   The Ux1 construction uses the step D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L563-L607
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L563-L607

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

theorem Formalism.FourierDecayAlt.P.Ux1.stepD {b : Bool} {X g : Mat k r} (hX : inLie k r X) (hg : g ∈ GV k r) (a : ℝ)
    (Hn : ℕ → Mat k r → E) (H0 H1 : Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hC : ∀ n, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Hn n))
    (h0 : ∀ n, ∀ h ∈ GV k r, ‖Hn n h - H0 h‖ ≤ gN h ^ (-a) * ε n)
    (h1 : ∀ n, ∀ h ∈ GV k r, ‖op b X (Hn n) h - H1 h‖ ≤ gN h ^ (-a) * ε n) :
    op b X H0 g = H1 g := by sorry
