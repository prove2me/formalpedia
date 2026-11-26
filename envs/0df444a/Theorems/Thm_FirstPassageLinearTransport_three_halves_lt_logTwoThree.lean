-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_three_halves_lt_logTwoThree
-- name    : FirstPassageLinearTransport.three_halves_lt_logTwoThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:21.921994+00:00
-- url     : https://prove2.me/theorems/9edfebbf-4c9b-45dd-84d2-9ad3b3c6d075
-- title:
--   First Passage Linear Transport: three halves lt log Two Three
-- statement:
--   A convenient rational separation from the central quarter-window.  This
--   is proved from `8 < 9`, so the later lattice argument does not depend on a
--   decimal approximation to `log₂ 3`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L176-L191
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L176-L191

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.three_halves_lt_logTwoThree : (3 / 2 : ℝ) < logTwoThree := by sorry
