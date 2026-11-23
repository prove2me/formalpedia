-- Prove2me | Theorems.Thm_Formalism_GrowthSums_KapPrime_u4
-- name    : Formalism.GrowthSums.KapPrime.u4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:45.039539+00:00
-- url     : https://prove2.me/theorems/efcab1f5-a7f3-4fd6-b250-791a33845549
-- title:
--   Kap Prime: u4
-- statement:
--   The Kap Prime construction uses the u4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L43-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L43-L64

import Mathlib
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_KapPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.GrowthSums
open Formalism.GrowthSums.KapPrime

theorem Formalism.GrowthSums.KapPrime.u4 {k Y Yb N La la a b' : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ N)
    (hla : 1 ≤ la) (hLa : 1 ≤ La) (hb0 : 0 < b') (ha : k * Y ^ 2 * Yb * N * La * la * b' ≤ a) :
    La * b' / a ≤ 1 / Y := by sorry
