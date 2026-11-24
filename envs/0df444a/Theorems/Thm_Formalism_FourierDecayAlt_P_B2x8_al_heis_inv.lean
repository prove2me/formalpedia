-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_heis_inv
-- name    : Formalism.FourierDecayAlt.P.B2x8.al_heis_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:57.882981+00:00
-- url     : https://prove2.me/theorems/ac99ef2e-54a5-4c97-a007-c927d6cef1fe
-- title:
--   B2x8: al heis inv
-- statement:
--   The B2x8 construction uses the al heis inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L933-L933
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L933-L933

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

theorem Formalism.FourierDecayAlt.P.B2x8.al_heis_inv (x : HPar k r') : (heis0 k r' x)⁻¹ = heis0 k r' (-x.1, -x.2) := by sorry
