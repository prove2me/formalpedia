-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassage_band
-- name    : FirstPassageLinearTransport.firstPassage_band
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:57.873596+00:00
-- url     : https://prove2.me/theorems/358eb15d-614b-4245-b51d-0796d192a6ae
-- title:
--   First Passage Linear Transport: first Passage band
-- statement:
--   The first-passage landing band in the division-free integer form
--   `Y < 2y` and `y ≤ Y`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L38-L49
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L38-L49

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.firstPassage_band {Y n h : ℕ} (hh : 0 < h)
    (hfp : IsFirstPassage Y n h) :
    Y < 2 * orbit h n ∧ orbit h n ≤ Y := by sorry
