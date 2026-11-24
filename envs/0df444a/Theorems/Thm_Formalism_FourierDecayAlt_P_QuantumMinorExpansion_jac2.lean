-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_jac2
-- name    : Formalism.FourierDecayAlt.P.QuantumMinorExpansion.jac2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:41.430738+00:00
-- url     : https://prove2.me/theorems/2fb14be8-baa5-46ec-8935-b2cfbf39b3d9
-- title:
--   Quantum Minor Expansion: jac2
-- statement:
--   The Quantum Minor Expansion construction uses the jac2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L325-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean#L325-L341

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

theorem Formalism.FourierDecayAlt.P.QuantumMinorExpansion.jac2 (hE : GlRel E) (u : ℂ) (i q j p : Fin (m + 2)) (hiq : i ≠ q) :
    qminor E (skip1 i) (skip1 j) (u + 1) * qminor E (skip1 q) (skip1 p) u -
        qminor E (skip1 q) (skip1 j) (u + 1) * qminor E (skip1 i) (skip1 p) u =
      if i = q ∨ j = p then 0 else
        ((eps i q * eps j p : ℤ) : A) *
          (qdet E (u + 1) * qminor E (skip2 (min i q) (max i q)) (skip2 (min j p) (max j p)) u) := by sorry
