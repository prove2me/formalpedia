-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_colExp
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorCommutation.colExp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:08:26.9318+00:00
-- url     : https://prove2.me/theorems/82d2f257-29f2-46b3-a297-53e2dc11313b
-- title:
--   Quantum Minor Commutation: col Exp
-- statement:
--   The Quantum Minor Commutation construction uses the col Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L68-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L68-L88

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorCommutation.colExp (hE : GlRel E) {m : ℕ} (a b : Fin (m + 1) → Fin n) (l₀ : Fin (m + 1)) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * Tm E (u - (m : ℂ)) (a l) (b l₀)) := by sorry
