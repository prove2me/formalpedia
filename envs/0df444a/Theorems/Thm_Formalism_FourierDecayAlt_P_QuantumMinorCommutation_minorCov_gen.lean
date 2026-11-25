-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_minorCov_gen
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_gen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:07:54.017899+00:00
-- url     : https://prove2.me/theorems/0e22821b-6086-40a1-80de-2bbc55d81bac
-- title:
--   Quantum Minor Commutation: minor Cov gen
-- statement:
--   The Quantum Minor Commutation construction uses the minor Cov gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L114-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L114-L131

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorCommutation
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_gen (hE : GlRel E) (η : Fin n → A) (hη : IsCov E η) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, b (l₀.succAbove k) ≠ b l₀) (u : ℂ) :
    qminor E a b u * η (b l₀) - η (b l₀) * qminor E a b u =
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * η (a l)) := by sorry
