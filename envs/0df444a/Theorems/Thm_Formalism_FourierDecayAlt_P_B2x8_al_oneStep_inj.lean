-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_oneStep_inj
-- name    : Formalism.FourierDecayAlt.P.B2x8.al_oneStep_inj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:57:40.493527+00:00
-- url     : https://prove2.me/theorems/65ced3fc-9a05-48d6-9805-bbb993852c26
-- title:
--   B2x8: al one Step inj
-- statement:
--   The B2x8 construction uses the al one Step inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1049-L1088
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1049-L1088

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

theorem Formalism.FourierDecayAlt.P.B2x8.al_oneStep_inj {x x' z z' : HPar k r'} {c : ℂ} (hc : c ≠ 0) {g₁ h₁ : Mat k r'}
    (h : oneStep k r' x c g₁ x' = oneStep k r' z c h₁ z') : x = z ∧ g₁ = h₁ ∧ x' = z' := by sorry
