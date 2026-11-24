-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cg_mem
-- name    : Formalism.FourierDecayAlt.P.B2x8.cg_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:57:51.514611+00:00
-- url     : https://prove2.me/theorems/161fb7ab-fef4-4fd6-b627-f6a2e7b6e5d1
-- title:
--   B2x8: cg mem
-- statement:
--   The B2x8 construction uses the cg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1333-L1345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1333-L1345

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

theorem Formalism.FourierDecayAlt.P.B2x8.cg_mem (R : ℝ) (hR : 0 ≤ R) (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) (h : ‖Ψt k r' p‖ ≤ R) : p ∈ cgS k r' R := by sorry
