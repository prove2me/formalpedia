-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_orb_of_int
-- name    : Formalism.FourierDecayAlt.P.A5x7.orb_of_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:18.191705+00:00
-- url     : https://prove2.me/theorems/f9fbbc96-7b4b-40b3-957b-c3b59315c109
-- title:
--   A5x7: orb of int
-- statement:
--   The A5x7 construction uses the orb of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L365-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L365-L394

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

theorem Formalism.FourierDecayAlt.P.A5x7.orb_of_int (w : Point K) (hw : InGLR R w) (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (h1 : p.1 ∈ intSub R (lowW K w.1 w.2)) (h2 : p.2 ∈ intSub R (upUniG K w.1.sum)) :
    IsInt R (orbZ w p) ∧ IsInt R (orbZ w p)⁻¹ ∧ orbZ w p * (orbZ w p)⁻¹ = 1 := by sorry
