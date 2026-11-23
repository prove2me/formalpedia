-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_sum_sub
-- name    : Formalism.FourierDecayAlt.P.A5x7.sum_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.644041+00:00
-- url     : https://prove2.me/theorems/8b6ab8c2-fc22-41c4-8650-d5ecf4d4cc28
-- title:
--   A5x7: sum sub
-- statement:
--   The A5x7 construction uses the sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L59-L68

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x7.sum_sub {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e) (f : Fin n → K)
    (hf : ∀ b, b ∉ Set.range e → f b = 0) : ∑ b, f b = ∑ i, f (e i) := by sorry
