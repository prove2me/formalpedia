-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_dual_base_vector
-- name    : Formalism.FourierDecayAlt.P.B2x8.heisenberg_dual_base_vector
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:56:39.493792+00:00
-- url     : https://prove2.me/theorems/edb6ae13-bb81-445c-80df-73900f606875
-- title:
--   B2x8: heisenberg dual base vector
-- statement:
--   The B2x8 construction uses the heisenberg dual base vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L956-L958
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L956-L958

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

theorem Formalism.FourierDecayAlt.P.B2x8.heisenberg_dual_base_vector (x : HPar k r') : heis0 k r' x *ᵥ es0 k r' = mk3 k r' (hb k r' x.1 x.2) x.1 1 := by sorry
