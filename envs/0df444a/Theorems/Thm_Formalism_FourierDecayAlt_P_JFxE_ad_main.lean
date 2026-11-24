-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ad_main
-- name    : Formalism.FourierDecayAlt.P.JFxE.ad_main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:01.772423+00:00
-- url     : https://prove2.me/theorems/fe337436-70e0-41ff-818f-a0af23ce54d7
-- title:
--   JFx E: ad main
-- statement:
--   The JFx E construction uses the ad main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L321-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L321-L378

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

theorem Formalism.FourierDecayAlt.P.JFxE.ad_main (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hQP : Q * P = 1)
    (hE : ∀ c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      Op c d φ g = ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ g)
    {t : ℕ} (e : Fin t ≃ Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Op e e u f g = qminorOp Eop e e u f g := by sorry
