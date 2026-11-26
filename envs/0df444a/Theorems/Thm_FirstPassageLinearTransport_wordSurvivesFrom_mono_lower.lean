-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordSurvivesFrom_mono_lower
-- name    : FirstPassageLinearTransport.wordSurvivesFrom_mono_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:16.768887+00:00
-- url     : https://prove2.me/theorems/a17cd2d2-3621-5583-8941-0fe86c7de800
-- title:
--   First Passage Linear Transport: word Survives From mono lower
-- statement:
--   Lowering a finite-word barrier preserves survival.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L145-L154
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L145-L154

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.wordSurvivesFrom_mono_lower
    {lo lo' : ℝ} {increment : Bool → ℝ} {r : ℕ} {z : ℝ}
    {v : Fin r → Bool} (hlo : lo' ≤ lo)
    (h : wordSurvivesFrom lo increment r z v) :
    wordSurvivesFrom lo' increment r z v := by sorry
