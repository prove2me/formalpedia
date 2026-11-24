-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_one_parameter_element_base_vector
-- name    : Formalism.FourierDecayAlt.P.B2x8.one_parameter_element_base_vector
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:01:43.789102+00:00
-- url     : https://prove2.me/theorems/04b2cadb-3d1b-4865-9635-dfa732de89a1
-- title:
--   B2x8: one parameter element base vector
-- statement:
--   The B2x8 construction uses the one parameter element base vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1031-L1037
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1031-L1037

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

theorem Formalism.FourierDecayAlt.P.B2x8.one_parameter_element_base_vector (x x' : HPar k r') (c : ℂ) (g₁ : Mat k r') :
    oneStep k r' x c g₁ x' *ᵥ e0 k r' = mk3 k r' (c * hb k r' (-x.1) (-x.2)) (c • (-x.1)) c := by sorry
