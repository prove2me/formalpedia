-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_inj_on
-- name    : Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_inj_on
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:59:52.828066+00:00
-- url     : https://prove2.me/theorems/461d1d3e-a1c7-4674-9921-1a510cbdf559
-- title:
--   B2x8: conj inverse map inj on
-- statement:
--   The B2x8 construction uses the conj inverse map inj on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L522-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L522-L529

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

theorem Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_inj_on (l : ℂ) (hl : l ≠ 0) : Set.InjOn (fun c : ℂ => l / conj c) {(0 : ℂ)}ᶜ := by sorry
