-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_eq_zero_of_psi
-- name    : Formalism.FourierDecayAlt.P.A5x3.eq_zero_of_psi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:37.900422+00:00
-- url     : https://prove2.me/theorems/ee162fe3-cfa9-4ad5-be15-6b841c07713a
-- title:
--   A5x3: eq zero of psi
-- statement:
--   The A5x3 construction uses the eq zero of psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L64-L72

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

theorem Formalism.FourierDecayAlt.P.A5x3.eq_zero_of_psi (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (y : KR R)
    (hy : ∀ r : R, psiKR R ψ (r • y) = 1) : y = 0 := by sorry
