-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_supp_one
-- name    : Formalism.FourierDecayAlt.P.A5x7.supp_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:42.745466+00:00
-- url     : https://prove2.me/theorems/c53c2eee-5ce0-4ba0-8f23-a8c1ec84056f
-- title:
--   A5x7: supp one
-- statement:
--   The A5x7 construction uses the supp one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L192-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L192-L219

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

theorem Formalism.FourierDecayAlt.P.A5x7.supp_one (h : Point K) (s : ℕ) (hs : 1 ≤ s) (t : Kˣ)
    (p : lowW K (addBlock h s t).1 (addBlock h s t).2 × upUniG K (addBlock h s t).1.sum)
    (hI : IsInt R (orbZ (addBlock h s t) p)) : (pt h.1 h.2).det * (t : K) ∈ R := by sorry
