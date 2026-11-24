-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BorderedDeterminants_sumBorder
-- name    : Formalism.FourierDecayAlt.P.BorderedDeterminants.sumBorder
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:35.924465+00:00
-- url     : https://prove2.me/theorems/ae1f0d43-5c81-4ba1-bedb-8bb022204481
-- title:
--   Bordered Determinants: sum Border
-- statement:
--   The Bordered Determinants construction uses the sum Border property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L145-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L145-L160

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

theorem Formalism.FourierDecayAlt.P.BorderedDeterminants.sumBorder {n : ℕ} (Y H : Fin n → Module.End ℂ V) (M : Fin n → Fin n → Module.End ℂ V)
    (Ψ : Fin n → Fin n → V) (c : Fin n → ℂ) (v : V) (h1 : ∀ x, ∑ i, Ψ i x = H x v)
    (h3 : ∀ i x : Fin n, ∑ a : Fin n, ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • M a x (Ψ i a) = c i • Ψ i x) :
    (∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) * (Y x * M w x * H w)) v =
      ∑ x, Y x (∑ i, c i • Ψ i x) := by sorry
