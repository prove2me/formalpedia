-- Prove2me | Theorems.Thm_Formalism_GrowthSums_KapPrime_u3
-- name    : Formalism.GrowthSums.KapPrime.u3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:43.200007+00:00
-- url     : https://prove2.me/theorems/9820192f-7632-4140-acc1-0f9de22a04fe
-- title:
--   Kap Prime: u3
-- statement:
--   The Kap Prime construction uses the u3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L31-L41

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

theorem Formalism.GrowthSums.KapPrime.u3 {k p Y La N₁ : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hN₁ : 1 ≤ N₁) (hp : k ^ 2 * Y ^ 2 ≤ p)
    (_hLa0 : 0 ≤ La) (hLa : La < k) : La * N₁ / p ≤ N₁ / Y := by sorry
