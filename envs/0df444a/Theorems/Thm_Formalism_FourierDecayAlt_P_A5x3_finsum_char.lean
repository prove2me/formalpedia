-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finsum_char
-- name    : Formalism.FourierDecayAlt.P.A5x3.finsum_char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:44.612807+00:00
-- url     : https://prove2.me/theorems/68702efb-4169-4cf7-860b-8f210d82c6e3
-- title:
--   A5x3: finsum char
-- statement:
--   The A5x3 construction uses the finsum char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L74-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L74-L83

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

theorem Formalism.FourierDecayAlt.P.A5x3.finsum_char {G : Type} [AddCommGroup G] [Finite G] (χ : AddChar G ℂ) :
    ((∀ g, χ g = 1) → ∑ᶠ g, χ g = (Nat.card G : ℂ)) ∧ ((∃ g, χ g ≠ 1) → ∑ᶠ g, χ g = 0) := by sorry
