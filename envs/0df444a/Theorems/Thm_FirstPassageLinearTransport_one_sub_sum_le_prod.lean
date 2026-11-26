-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_one_sub_sum_le_prod
-- name    : FirstPassageLinearTransport.one_sub_sum_le_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:54.22434+00:00
-- url     : https://prove2.me/theorems/6e6d3e51-1881-4a9a-b3b5-aa11dba3f696
-- title:
--   First Passage Linear Transport: one sub sum le prod
-- statement:
--   Elementary finite-product form of `prod (1-u_i) ≥ 1-sum u_i`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L192-L212
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L192-L212

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.one_sub_sum_le_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by sorry
