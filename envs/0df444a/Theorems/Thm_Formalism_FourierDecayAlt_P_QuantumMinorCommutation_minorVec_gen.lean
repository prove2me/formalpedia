-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_minorVec_gen
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorVec_gen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:22.766717+00:00
-- url     : https://prove2.me/theorems/fc133bb1-a815-4e8b-8775-3ecddf247e75
-- title:
--   Quantum Minor Commutation: minor Vec gen
-- statement:
--   The Quantum Minor Commutation construction uses the minor Vec gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L90-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L90-L112

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorVec_gen (hE : GlRel E) (y : Fin n → A) (hy : IsVec E y) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, a (l₀.succAbove k) ≠ a l₀) (u : ℂ) :
    qminor E a b u * y (a l₀) = y (a l₀) * qminor E a b u -
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (y (b l) * qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by sorry
