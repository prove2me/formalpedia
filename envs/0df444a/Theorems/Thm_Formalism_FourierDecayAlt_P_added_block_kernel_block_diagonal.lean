-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_added_block_kernel_block_diagonal
-- name    : Formalism.FourierDecayAlt.P.added_block_kernel_block_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:53.373437+00:00
-- url     : https://prove2.me/theorems/600b80a5-f2bd-4b5d-b771-3c47a475dec0
-- title:
--   P: added block kernel block diagonal
-- statement:
--   The P construction uses the added block kernel block diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L926-L928
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L926-L928

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x5

theorem Formalism.FourierDecayAlt.P.added_block_kernel_block_diagonal : Formalism.FourierDecayAlt.A5.NsBlockDiag := by sorry
