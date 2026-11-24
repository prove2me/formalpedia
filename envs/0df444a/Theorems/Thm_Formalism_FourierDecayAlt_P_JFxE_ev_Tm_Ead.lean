-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_Tm_Ead
-- name    : Formalism.FourierDecayAlt.P.JFxE.ev_Tm_Ead
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:01.774807+00:00
-- url     : https://prove2.me/theorems/e75cb32a-1065-439f-88e0-ef72619f64b6
-- title:
--   JFx E: ev Tm Ead
-- statement:
--   The JFx E construction uses the ev Tm Ead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L314-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L314-L319

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

theorem Formalism.FourierDecayAlt.P.JFxE.ev_Tm_Ead (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : ℂ) (c d : Fin (2 * r + k + 1))
    (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ x =
      (if c = d then v • φ x else 0) + ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ x := by sorry
