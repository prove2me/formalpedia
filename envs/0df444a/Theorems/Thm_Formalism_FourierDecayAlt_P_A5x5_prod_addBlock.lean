-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_prod_addBlock
-- name    : Formalism.FourierDecayAlt.P.A5x5.prod_addBlock
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:42.495801+00:00
-- url     : https://prove2.me/theorems/c920f7af-08a3-4cc4-9934-beb9f9282dea
-- title:
--   A5x5: prod add Block
-- statement:
--   The A5x5 construction uses the prod add Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L825-L849
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L825-L849

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
variable {K : Type} [CommRing K] {R : Subring K}

theorem Formalism.FourierDecayAlt.P.A5x5.prod_addBlock (h : Point K) (s : ℕ) (t : Kˣ) :
    (∏ a : Fin (addBlock h s t).1.sum,
      (((addBlock h s t).2 (blk (addBlock h s t).1 a) : Kˣ) : K)) =
      (∏ a : Fin h.1.sum, ((h.2 (blk h.1 a) : Kˣ) : K)) * (t : K) ^ s := by sorry
