-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_reindex
-- name    : Formalism.FourierDecayAlt.P.A5x5.dl_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:58.621572+00:00
-- url     : https://prove2.me/theorems/0a65b926-12a7-454b-bdee-767ae0e77b59
-- title:
--   A5x5: dl reindex
-- statement:
--   The A5x5 construction uses the dl reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L429-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L429-L461

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

theorem Formalism.FourierDecayAlt.P.A5x5.dl_reindex (e : ι ≃ κ) (M : Matrix ι ι K) : dl R (reindex e e M) = dl R M := by sorry
