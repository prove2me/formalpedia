-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_bridge_fold
-- name    : Formalism.FourierDecayAlt.P.JFxE.bridge_fold
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:55.366953+00:00
-- url     : https://prove2.me/theorems/dd390558-a800-49d2-bf88-afbb7587c544
-- title:
--   JFx E: bridge fold
-- statement:
--   The JFx E construction uses the bridge fold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L49-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BridgeQminor.lean#L49-L75

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

theorem Formalism.FourierDecayAlt.P.JFxE.bridge_fold (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g) :
    ∀ (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E),
      CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r,
        ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f g =
          (ts.map fun t => Top Op t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g := by sorry
