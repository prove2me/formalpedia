-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_psiKR_zero
-- name    : Formalism.FourierDecayAlt.P.A5x3.psiKR_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:55.496306+00:00
-- url     : https://prove2.me/theorems/04695c03-1820-49dc-8ab4-5dbaca80dbc2
-- title:
--   A5x3: psi KR zero
-- statement:
--   The A5x3 construction uses the psi KR zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L165-L166

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
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable {C : Type} [AddCommGroup C] [Module R C]

theorem Formalism.FourierDecayAlt.P.A5x3.psiKR_zero (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) :
    psiKR R ψ (0 : KR R) = 1 := by sorry
