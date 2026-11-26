-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzSurvivalMass_le_fullWordBins
-- name    : FirstPassageLinearTransport.collatzSurvivalMass_le_fullWordBins
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:50.659053+00:00
-- url     : https://prove2.me/theorems/f210d410-0bdf-5064-a79b-e4ba3176b24f
-- title:
--   First Passage Linear Transport: collatz Survival Mass le full Word Bins
-- statement:
--   Survival mass is covered by the finite sum of canonical terminal bins.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L291-L331
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L291-L331

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.collatzSurvivalMass_le_fullWordBins
    {m Q : ℕ} {B : ℝ}
    (hQ : m + ⌈B⌉₊ + 2 ≤ Q) :
    weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 ≤
      ∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B (q : ℝ) := by sorry
