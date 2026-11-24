-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_quantum_minor_expansion_second_sum
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorExpansion.quantum_minor_expansion_second_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:57.71228+00:00
-- url     : https://prove2.me/theorems/28f6f751-2644-4acc-9664-e4442cb4f0a3
-- title:
--   Quantum Minor Expansion: quantum minor expansion second sum
-- statement:
--   The Quantum Minor Expansion construction uses the quantum minor expansion second sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L172-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L172-L192

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorExpansion.quantum_minor_expansion_second_sum (hE : GlRel E) (q : Fin (m + 2)) (i' : Fin (m + 1)) (q' : Fin (m + 1))
    (hq' : (q.succAbove i').succAbove q' = q) (j c : Fin (m + 2)) (u : ℂ) :
    ∑ x : Fin (m + 1), ((-1 : ℤ) ^ (x : ℕ)) •
        (qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u * Tm E (u + 1) c (j.succAbove x)) =
      (if c = q.succAbove i' then ((-1 : ℤ) ^ (i' : ℕ)) • qminor E q.succAbove j.succAbove (u + 1) else 0) +
        (if c = q then ((-1 : ℤ) ^ (q' : ℕ)) • qminor E (q.succAbove i').succAbove j.succAbove (u + 1) else 0) := by sorry
