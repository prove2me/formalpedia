-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_detVec_succ
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorCommutation.detVec_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:09:55.095465+00:00
-- url     : https://prove2.me/theorems/1aae08af-4faf-4db4-87a0-1e21f484d1f9
-- title:
--   Quantum Minor Commutation: det Vec succ
-- statement:
--   The Quantum Minor Commutation construction uses the det Vec succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorCommutation.lean#L160-L168

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorCommutation.detVec_succ {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (y : Fin (m + 1) → A) (hE : GlRel E) (hy : IsVec E y) (w : ℂ) (j : Fin (m + 1)) :
    qdet E w * y j = y j * qdet E w -
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((j : ℕ) + (l : ℕ)) : ℤ) : A) *
        (y l * qminor (t := m) E (skip1 j) (skip1 l) w) := by sorry
