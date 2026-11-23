-- Prove2me | Theorems.Thm_Formalism_GrowthSums_KapPrime_u5
-- name    : Formalism.GrowthSums.KapPrime.u5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:19.710802+00:00
-- url     : https://prove2.me/theorems/1fdc335e-5721-4b3e-a0e5-7ab97aa8e071
-- title:
--   Kap Prime: u5
-- statement:
--   The Kap Prime construction uses the u5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L66-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/KapPrime.lean#L66-L84

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

theorem Formalism.GrowthSums.KapPrime.u5 {Cc k N N₁ Q c a Y Z : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) (hQ : 1 ≤ Q)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (hc0 : 0 ≤ c) (hc : c ≤ 2 * Cc * Z)
    (ha : k ^ 3 * N * Q ^ 4 * Z * Y ≤ a) :
    k ^ 3 * N₁ * Q ^ 2 * c / a ≤ 2 * Cc * N₁ / (N * Y) := by sorry
