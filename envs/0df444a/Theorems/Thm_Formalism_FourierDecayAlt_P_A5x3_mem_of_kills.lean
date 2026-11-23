-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mem_of_kills
-- name    : Formalism.FourierDecayAlt.P.A5x3.mem_of_kills
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:57.725836+00:00
-- url     : https://prove2.me/theorems/a6a85248-a81e-4614-a380-f653a4679ecf
-- title:
--   A5x3: mem of kills
-- statement:
--   The A5x3 construction uses the mem of kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L168-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L168-L207

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

theorem Formalism.FourierDecayAlt.P.A5x3.mem_of_kills (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (S : Submodule R (C →ₗ[R] KR R)) (μ : C →ₗ[R] KR R)
    (hμ : ∀ c, (∀ α ∈ S, α c = 0) → μ c = 0) : μ ∈ S := by sorry
