-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_coker
-- name    : Formalism.FourierDecayAlt.P.A5x3.finite_coker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:23.338237+00:00
-- url     : https://prove2.me/theorems/7b03b562-20cf-4492-9c6e-d5ddbc517853
-- title:
--   A5x3: finite coker
-- statement:
--   The A5x3 construction uses the finite coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L319-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L319-L321

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A5x3.finite_coker (hD : LocalDatum K R ψ) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (hZ : IsInt R Z) (hdet : IsUnit Z.det) : Finite (coker R Z) := by sorry
