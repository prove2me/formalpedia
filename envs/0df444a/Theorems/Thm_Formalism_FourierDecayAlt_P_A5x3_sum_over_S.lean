-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_sum_over_S
-- name    : Formalism.FourierDecayAlt.P.A5x3.sum_over_S
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:59.2078+00:00
-- url     : https://prove2.me/theorems/5f7f00a5-d618-484d-a7af-1c8f6aedc7f5
-- title:
--   A5x3: sum over S
-- statement:
--   The A5x3 construction uses the sum over S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L138-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L138-L156

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
open Classical

theorem Formalism.FourierDecayAlt.P.A5x3.sum_over_S (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (S : Submodule R (C →ₗ[R] KR R)) (c : C) :
    ∑ᶠ α : S, psiKR R ψ ((α : C →ₗ[R] KR R) c) =
      if ∀ α ∈ S, α c = 0 then (Nat.card S : ℂ) else 0 := by sorry
