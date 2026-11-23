-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_det_orbZ
-- name    : Formalism.FourierDecayAlt.P.A5x5.det_orbZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:01.236009+00:00
-- url     : https://prove2.me/theorems/fca6066d-7a4d-4990-a190-9d59df6cfa3a
-- title:
--   A5x5: det orb Z
-- statement:
--   The A5x5 construction uses the det orb Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L773-L778
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L773-L778

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

theorem Formalism.FourierDecayAlt.P.A5x5.det_orbZ (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    (orbZ w p).det = (pt w.1 w.2).det := by sorry
