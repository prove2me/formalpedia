-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_quantum_minor_expansion_first_sum
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorExpansion.quantum_minor_expansion_first_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:57.586127+00:00
-- url     : https://prove2.me/theorems/d9172226-efad-472a-9dac-cf81489c5737
-- title:
--   Quantum Minor Expansion: quantum minor expansion first sum
-- statement:
--   The Quantum Minor Expansion construction uses the quantum minor expansion first sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L165-L170

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)

theorem Formalism.FourierDecayAlt.P.QuantumMinorExpansion.quantum_minor_expansion_first_sum (hE : GlRel E) (q c : Fin (m + 2)) (u : ℂ) :
    ∑ p : Fin (m + 2), ((-1 : ℤ) ^ (p : ℕ)) • (qminor E q.succAbove p.succAbove u * Tm E (u + 1) c p) =
      if c = q then ((-1 : ℤ) ^ (q : ℕ)) • qdet E (u + 1) else 0 := by sorry
