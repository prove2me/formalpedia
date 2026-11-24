-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sk_perm
-- name    : Formalism.FourierDecayAlt.P.JFxE.sk_perm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:59:06.671752+00:00
-- url     : https://prove2.me/theorems/046b6c92-e65e-4e18-a929-15b3534d5978
-- title:
--   JFx E: sk perm
-- statement:
--   The JFx E construction uses the sk perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L251-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L251-L280

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

theorem Formalism.FourierDecayAlt.P.JFxE.sk_perm (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (τ : Equiv.Perm (Fin t)) :
    ∀ (b : Fin t → Fin (2 * r + k + 1)), ∀ g ∈ GV k r,
      ev Eop (qminor (Lf k r E) a (b ∘ τ) u) f g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g := by sorry
