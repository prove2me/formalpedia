-- Prove2me | Theorems.Thm_Formalism_GrowthSums_KapPrime_u1
-- name    : Formalism.GrowthSums.KapPrime.u1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:42.540392+00:00
-- url     : https://prove2.me/theorems/8db82476-0cdb-48ea-b65e-f04eae9fe18a
-- title:
--   Kap Prime: u1
-- statement:
--   The Kap Prime construction uses the u1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L9-L16

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

theorem Formalism.GrowthSums.KapPrime.u1 {k p Y : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hp : k ^ 2 * Y ^ 2 ≤ p) : k / p ^ 2 ≤ 1 / Y := by sorry
