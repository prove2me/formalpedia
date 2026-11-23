-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_of_le
-- name    : Formalism.FourierDecayAlt.P.A5x5.gi_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:02.587983+00:00
-- url     : https://prove2.me/theorems/3e3c3282-95d6-4504-97f1-6500ee04455f
-- title:
--   A5x5: gi of le
-- statement:
--   The A5x5 construction uses the gi of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L20-L34

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {V W : Type} [AddCommGroup V] [AddCommGroup W]

theorem Formalism.FourierDecayAlt.P.A5x5.gi_of_le {A B D : AddSubgroup V} (hA : D ≤ A) (hB : D ≤ B) (hDA : D.relIndex A ≠ 0)
    (hDB : D.relIndex B ≠ 0) : gi A B = (D.relIndex A : ℝ) / (D.relIndex B : ℝ) := by sorry
