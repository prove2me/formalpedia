-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
-- name    : Formalism.FourierDecayAlt.P.A5x3.mk_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:39.89991+00:00
-- url     : https://prove2.me/theorems/65c068e1-b3c3-4684-856d-bd2889a0208c
-- title:
--   A5x3: mk eq zero
-- statement:
--   The A5x3 construction uses the mk eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L20-L21

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

theorem Formalism.FourierDecayAlt.P.A5x3.mk_eq_zero (x : K) : (Submodule.Quotient.mk x : KR R) = 0 ↔ x ∈ R := by sorry
