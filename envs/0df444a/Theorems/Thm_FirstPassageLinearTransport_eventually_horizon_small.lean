-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_horizon_small
-- name    : FirstPassageLinearTransport.eventually_horizon_small
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:44.121217+00:00
-- url     : https://prove2.me/theorems/131c0258-8f81-45ba-86b1-721fb4412d30
-- title:
--   First Passage Linear Transport: eventually horizon small
-- statement:
--   The First Passage Linear Transport construction uses the eventually horizon small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parameters.lean#L33-L83
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parameters.lean#L33-L83

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_Parameters
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_horizon_small {r : ℝ} (hr : 0 < r) :
    ∀ᶠ M : ℕ in Filter.atTop,
      (M : ℝ) / (2 * (targetScale r M : ℝ)) ≤ 1 / 3 := by sorry
