-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chS_apply
-- name    : Formalism.FourierDecayAlt.P.A5x3.chS_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:41.466347+00:00
-- url     : https://prove2.me/theorems/a1f0475d-9472-4e70-bb9f-2d532d87864f
-- title:
--   A5x3: ch S apply
-- statement:
--   The A5x3 construction uses the ch S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L132-L134

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

theorem Formalism.FourierDecayAlt.P.A5x3.chS_apply (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (S : Submodule R (C →ₗ[R] KR R)) (c : C) (α : S) :
    chS h S c α = psiKR R ψ ((α : C →ₗ[R] KR R) c) := by sorry
