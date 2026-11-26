-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellInitialWindowBad_subset_maximal
-- name    : FirstPassageLinearTransport.shellInitialWindowBad_subset_maximal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:06:52.825987+00:00
-- url     : https://prove2.me/theorems/d97327c9-6c10-4b75-8551-daf0fc27fcdb
-- title:
--   First Passage Linear Transport: shell Initial Window Bad subset maximal
-- statement:
--   The First Passage Linear Transport construction uses the shell Initial Window Bad subset maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L142-L158
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L142-L158

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shellInitialWindowBad_subset_maximal
    {M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (maximalBarrierHeight t M) := by sorry
