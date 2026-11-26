-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_initialWindowGood_subset_extendedWindow
-- name    : FirstPassageLinearTransport.initialWindowGood_subset_extendedWindow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:42.590501+00:00
-- url     : https://prove2.me/theorems/27fee341-6103-4123-9fda-baceb07c1fcf
-- title:
--   First Passage Linear Transport: initial Window Good subset extended Window
-- statement:
--   The First Passage Linear Transport construction uses the initial Window Good subset extended Window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L104-L107
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L104-L107

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.initialWindowGood_subset_extendedWindow {r eta : ℝ}
    (p : StageSetup r eta) :
    initialWindowGood eta ⊆ extendedWindow p := by sorry
