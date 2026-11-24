-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_sum_split_first_middle_last
-- name    : Formalism.FourierDecayAlt.P.B2x8.sum_split_first_middle_last
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:17.268812+00:00
-- url     : https://prove2.me/theorems/540f8233-5dc3-4ea9-a1b2-7093c8767ade
-- title:
--   B2x8: sum split first middle last
-- statement:
--   The B2x8 construction uses the sum split first middle last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L136-L140

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.sum_split_first_middle_last {N n : ℕ} (h : N = n + 2) (f : Fin N → ℂ) :
    ∑ i, f i = f ⟨0, by omega⟩ + ∑ j : Fin n, f ⟨j.val + 1, by omega⟩ + f ⟨n + 1, by omega⟩ := by sorry
