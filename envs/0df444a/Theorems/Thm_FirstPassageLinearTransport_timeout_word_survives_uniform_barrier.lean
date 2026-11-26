-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_word_survives_uniform_barrier
-- name    : FirstPassageLinearTransport.timeout_word_survives_uniform_barrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:22.947951+00:00
-- url     : https://prove2.me/theorems/2a01db02-9270-4ee5-ad69-f852e7e09d53
-- title:
--   First Passage Linear Transport: timeout word survives uniform barrier
-- statement:
--   Every literal timeout word in a fixed low-rank window survives one
--   barrier depending only on the window constants.  The extra two rank units
--   come from the uniform affine-orbit comparison above.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L187-L211
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L187-L211

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeout_word_survives_uniform_barrier
    {K₀ C : ℝ} {L m x : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ))
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    wordSurvivesFrom
      (-((C * K₀ / 2 + 3) * Real.log 2))
      collatzLogIncrement m 0 (boolParityWord m x) := by sorry
