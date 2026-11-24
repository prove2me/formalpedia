-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_rel
-- name    : Formalism.FourierDecayAlt.P.JFxE.ev_rel
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:55.370797+00:00
-- url     : https://prove2.me/theorems/3eb4093d-3fb8-4276-a4d1-3db7fce48e0f
-- title:
--   JFx E: ev rel
-- statement:
--   The JFx E construction uses the ev rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L114-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L114-L136

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem Formalism.FourierDecayAlt.P.JFxE.ev_rel (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (a b c d : Fin (2 * r + k + 1)) (ψ : Mat k r → E) (hψ : CkOn 2 (GV k r) ψ) :
    ∀ g ∈ GV k r, ev Eop (rel (Lf k r E) a b c d) ψ g = 0 := by sorry
