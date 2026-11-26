-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_initialWindowGood_powerDense
-- name    : FirstPassageLinearTransport.initialWindowGood_powerDense
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:13.169798+00:00
-- url     : https://prove2.me/theorems/970ab26a-73ee-5c8a-9131-28ac58a1a8e3
-- title:
--   First Passage Linear Transport: initial Window Good power Dense
-- statement:
--   The maximal-barrier set is quantitatively dense.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L278-L296
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L278-L296

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.initialWindowGood_powerDense
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    PowerDense (initialWindowGood t)
      (quadraticWindowGlobalConstant t)
      (quadraticWindowDensityRate t) := by sorry
