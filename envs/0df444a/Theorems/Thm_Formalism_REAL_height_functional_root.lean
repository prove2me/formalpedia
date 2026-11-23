-- Prove2me | Theorems.Thm_Formalism_REAL_height_functional_root
-- name    : Formalism.REAL.height_functional_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:09.59239+00:00
-- url     : https://prove2.me/theorems/256eca3e-9862-44a5-958e-a3c03b107fa8
-- title:
--   REAL: height functional root
-- statement:
--   The REAL construction uses the height functional root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L75-L77

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem Formalism.REAL.height_functional_root {m : ℕ} (c d : Fin m) :
    heightFunctional (Pi.single c (1 : ℝ) - Pi.single d 1) = (c : ℝ) - d := by sorry
