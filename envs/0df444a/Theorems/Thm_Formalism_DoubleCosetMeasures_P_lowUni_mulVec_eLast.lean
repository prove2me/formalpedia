-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_lowUni_mulVec_eLast
-- name    : Formalism.DoubleCosetMeasures.P.lowUni_mulVec_eLast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:43.564037+00:00
-- url     : https://prove2.me/theorems/dc838005-c8dd-4700-97d5-bace5861d6ac
-- title:
--   P: low Uni mul Vec e Last
-- statement:
--   The P construction uses the low Uni mul Vec e Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L51-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L51-L76

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.lowUni_mulVec_eLast {M : Matrix (Fin n) (Fin n) K} (h : IsLowUni M) :
    M *ᵥ coeLin R (eLast R) = coeLin R (eLast R) := by sorry
