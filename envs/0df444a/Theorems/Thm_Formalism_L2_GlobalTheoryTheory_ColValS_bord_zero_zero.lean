-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_zero
-- name    : Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:15.855749+00:00
-- url     : https://prove2.me/theorems/82a430ca-4f89-44ff-b94a-89f20d1114e5
-- title:
--   Col Val S: bord zero zero
-- statement:
--   The Col Val S construction uses the bord zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]

theorem Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : bord M 0 0 = 1 := by sorry
