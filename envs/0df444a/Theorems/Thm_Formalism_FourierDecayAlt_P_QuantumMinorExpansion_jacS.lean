-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_jacS
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorExpansion.jacS
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:08.389923+00:00
-- url     : https://prove2.me/theorems/0c7ffdf5-65e8-4f3a-a1ab-fbad0b1f7a37
-- title:
--   Quantum Minor Expansion: jac S
-- statement:
--   The Quantum Minor Expansion construction uses the jac S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L290-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L290-L323

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorExpansion.jacS (hE : GlRel E) (u : ℂ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2)) :
    (qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove j.succAbove u -
      qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove j.succAbove u = 0) ∧
    ∀ x : Fin (m + 1),
      qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove (j.succAbove x).succAbove u -
        qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove (j.succAbove x).succAbove u =
      ((eps (q.succAbove i') q * eps j (j.succAbove x) : ℤ) : A) *
        (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u) := by sorry
