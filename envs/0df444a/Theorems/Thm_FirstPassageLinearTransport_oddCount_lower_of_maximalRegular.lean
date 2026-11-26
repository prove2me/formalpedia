-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_lower_of_maximalRegular
-- name    : FirstPassageLinearTransport.oddCount_lower_of_maximalRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:24.725591+00:00
-- url     : https://prove2.me/theorems/21cc3f78-32c7-54a6-91f6-293ac4d3fad8
-- title:
--   First Passage Linear Transport: odd Count lower of maximal Regular
-- statement:
--   The First Passage Linear Transport construction uses the odd Count lower of maximal Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L147-L152
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L147-L152

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.oddCount_lower_of_maximalRegular {n M H : ℕ} {h : ℝ}
    (hreg : MaximalParityRegular n M h) (hHM : H ≤ M) :
    (H : ℝ) / 2 - h ≤ oddCount n H := by sorry
