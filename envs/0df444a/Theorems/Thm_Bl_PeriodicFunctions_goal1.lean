-- Prove2me | Theorems.Thm_Bl_PeriodicFunctions_goal1
-- name    : Bl.PeriodicFunctions.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:35.626317+00:00
-- url     : https://prove2.me/theorems/868c46c2-6461-4976-8df2-9618b83138f4
-- title:
--   Periodic Functions: goal1
-- statement:
--   The Periodic Functions construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PeriodicFunctions/PeriodicApplyMulAdd.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PeriodicFunctions/PeriodicApplyMulAdd.lean#L16-L24

import Mathlib
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
open Bl Bl.PeriodicFunctions
variable {K : Type} [Field K]

theorem Bl.PeriodicFunctions.goal1 (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by sorry
