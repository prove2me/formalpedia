-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chC_apply
-- name    : Formalism.FourierDecayAlt.P.A5x3.chC_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:33.189615+00:00
-- url     : https://prove2.me/theorems/f6b7a00d-1c51-4cca-86d7-3cfe13dddee2
-- title:
--   A5x3: ch C apply
-- statement:
--   The A5x3 construction uses the ch C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L90-L91

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
variable {C : Type} [AddCommGroup C] [Module R C]

theorem Formalism.FourierDecayAlt.P.A5x3.chC_apply (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (μ : C →ₗ[R] KR R) (c : C) :
    chC h μ c = psiKR R ψ (μ c) := by sorry
