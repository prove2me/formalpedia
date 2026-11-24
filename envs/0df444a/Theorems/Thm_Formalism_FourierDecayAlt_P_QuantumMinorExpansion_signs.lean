-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_signs
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorExpansion.signs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:35.83486+00:00
-- url     : https://prove2.me/theorems/ca643b58-5852-45bf-911c-a132121d892f
-- title:
--   Quantum Minor Expansion: signs
-- statement:
--   The Quantum Minor Expansion construction uses the signs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L243-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L243-L254

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorExpansion.signs (q : Fin (m + 2)) (i' q' : Fin (m + 1)) (hq' : (q.succAbove i').succAbove q' = q) :
    (-eps (q.succAbove i') q) * (-1) ^ (q' : ℕ) = (-1) ^ (q : ℕ) ∧
      (-eps (q.succAbove i') q) * (-1) ^ (i' : ℕ) = -(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ) := by sorry
