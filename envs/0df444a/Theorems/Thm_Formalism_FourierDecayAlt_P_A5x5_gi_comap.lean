-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_comap
-- name    : Formalism.FourierDecayAlt.P.A5x5.gi_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:44.690237+00:00
-- url     : https://prove2.me/theorems/18578a0d-2834-48c7-8b38-73e39f799433
-- title:
--   A5x5: gi comap
-- statement:
--   The A5x5 construction uses the gi comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L51-L61

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

theorem Formalism.FourierDecayAlt.P.A5x5.gi_comap (f : V →+ W) (A L : AddSubgroup V) (A' L' : AddSubgroup W)
    (h1 : ∀ v ∈ L, v ∈ A ↔ f v ∈ A') (h2 : ∀ v ∈ A, v ∈ L ↔ f v ∈ L')
    (h3 : L.map f = L') (h4 : A.map f = A') : gi A L = gi A' L' := by sorry
