-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BorderedDeterminants_sumBorder_zero
-- name    : Formalism.FourierDecayAlt.P.BorderedDeterminants.sumBorder_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:25.869791+00:00
-- url     : https://prove2.me/theorems/2cce6c52-d536-49aa-adc9-37fda8540b05
-- title:
--   Bordered Determinants: sum Border zero
-- statement:
--   The Bordered Determinants construction uses the sum Border zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L162-L170

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.BorderedDeterminants.sumBorder_zero {n : ℕ} (Y : Fin n → Module.End ℂ V) (Ψ : Fin n → Fin n → V) (c : Fin n → ℂ) (i : Fin n)
    (hΨ : ∀ x, Ψ i x = 0) (hc : ∀ i', i' ≠ i → c i' = 0) : ∑ x, Y x (∑ i', c i' • Ψ i' x) = 0 := by sorry
