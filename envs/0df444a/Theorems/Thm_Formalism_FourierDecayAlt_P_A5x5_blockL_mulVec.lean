-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blockL_mulVec
-- name    : Formalism.FourierDecayAlt.P.A5x5.blockL_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:58.254715+00:00
-- url     : https://prove2.me/theorems/e23a904e-349e-41e7-bf36-43767d607670
-- title:
--   A5x5: block L mul Vec
-- statement:
--   The A5x5 construction uses the block L mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L278-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L278-L281

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
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}

theorem Formalism.FourierDecayAlt.P.A5x5.blockL_mulVec (S : Matrix ι ι K) (w : ι ⊕ Unit → K) :
    fromBlocks S 0 0 (1 : Matrix Unit Unit K) *ᵥ w =
      Sum.elim (S *ᵥ (w ∘ Sum.inl)) (w ∘ Sum.inr) := by sorry
