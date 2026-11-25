-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_minorCov_succ
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:18.116368+00:00
-- url     : https://prove2.me/theorems/e3a847a9-2423-4ace-ae87-b71ef05c4ce7
-- title:
--   Quantum Minor Commutation: minor Cov succ
-- statement:
--   The Quantum Minor Commutation construction uses the minor Cov succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L170-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L170-L184

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_succ {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
    (η : Fin (m + 2) → A) (hE : GlRel E) (hη : IsCov E η) (u : ℂ) (q p i : Fin (m + 2)) (hip : i ≠ p) :
    qminor (t := m + 1) E (skip1 q) (skip1 p) u * η i - η i * qminor (t := m + 1) E (skip1 q) (skip1 p) u =
      ∑ a : Fin (m + 2), if a = q then 0 else
        ((eps a q * eps i p * (-1) ^ ((a : ℕ) + (i : ℕ)) : ℤ) : A) *
          (qminor (t := m) E (skip2 (min a q) (max a q)) (skip2 (min i p) (max i p)) u * η a) := by sorry
