-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
-- name    : Formalism.FourierDecayAlt.P.A5x5.relIndex_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:20.900259+00:00
-- url     : https://prove2.me/theorems/ee1488ea-7da4-42b2-8ca3-4cd5208352d3
-- title:
--   A5x5: rel Index ne zero
-- statement:
--   The A5x5 construction uses the rel Index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L69-L75

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
variable [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem Formalism.FourierDecayAlt.P.A5x5.relIndex_ne_zero {U A : AddSubgroup V} (hU : IsOpen (U : Set V))
    (hA : IsCompact (A : Set V)) : U.relIndex A ≠ 0 := by sorry
