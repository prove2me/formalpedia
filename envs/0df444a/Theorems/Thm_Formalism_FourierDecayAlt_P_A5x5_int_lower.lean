-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_int_lower
-- name    : Formalism.FourierDecayAlt.P.A5x5.int_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:02.352803+00:00
-- url     : https://prove2.me/theorems/477e401f-7828-43e1-af27-77e0af42f926
-- title:
--   A5x5: int lower
-- statement:
--   The A5x5 construction uses the int lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L505-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L505-L511

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
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}

theorem Formalism.FourierDecayAlt.P.A5x5.int_lower {s : Matrix Unit ι K} (hs : ∀ i, s () i ∈ R) (a b : ι ⊕ Unit) :
    (fromBlocks (1 : Matrix ι ι K) 0 s (1 : Matrix Unit Unit K)) a b ∈ R := by sorry
