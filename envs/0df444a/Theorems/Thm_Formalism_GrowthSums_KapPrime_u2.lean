-- Prove2me | Theorems.Thm_Formalism_GrowthSums_KapPrime_u2
-- name    : Formalism.GrowthSums.KapPrime.u2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:41.847794+00:00
-- url     : https://prove2.me/theorems/0a729876-7421-4b24-8411-f76419bd315e
-- title:
--   Kap Prime: u2
-- statement:
--   The Kap Prime construction uses the u2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L18-L29

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

theorem Formalism.GrowthSums.KapPrime.u2 {k p Y a b' : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hp : k ^ 2 * Y ^ 2 ≤ p) (hb0 : 0 < b')
    (hab : b' ≤ a) : k * b' / (p * a) ≤ 1 / Y := by sorry
