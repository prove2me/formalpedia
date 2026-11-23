-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_int_of_orb
-- name    : Formalism.FourierDecayAlt.P.A5x7.int_of_orb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:22.065397+00:00
-- url     : https://prove2.me/theorems/1e80b5b3-b28d-4624-943d-e71ea78ee94e
-- title:
--   A5x7: int of orb
-- statement:
--   The A5x7 construction uses the int of orb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L333-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L333-L363

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

theorem Formalism.FourierDecayAlt.P.A5x7.int_of_orb (w : Point K) (hw : InGLR R w) (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (hZ : IsInt R (orbZ w p)) :
    p.1 ∈ intSub R (lowW K w.1 w.2) ∧ p.2 ∈ intSub R (upUniG K w.1.sum) := by sorry
