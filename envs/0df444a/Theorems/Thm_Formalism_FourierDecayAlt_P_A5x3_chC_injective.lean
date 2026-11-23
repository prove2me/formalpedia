-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chC_injective
-- name    : Formalism.FourierDecayAlt.P.A5x3.chC_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:30.654797+00:00
-- url     : https://prove2.me/theorems/221224dc-5879-4232-b67a-edff137a0bc0
-- title:
--   A5x3: ch C injective
-- statement:
--   The A5x3 construction uses the ch C injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L93-L104

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

theorem Formalism.FourierDecayAlt.P.A5x3.chC_injective (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) :
    Function.Injective (chC h : (C →ₗ[R] KR R) → AddChar C ℂ) := by sorry
