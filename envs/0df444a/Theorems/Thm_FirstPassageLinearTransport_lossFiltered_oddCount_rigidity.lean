-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFiltered_oddCount_rigidity
-- name    : FirstPassageLinearTransport.lossFiltered_oddCount_rigidity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:46.8416+00:00
-- url     : https://prove2.me/theorems/0dd4b9ab-81bb-4c15-b6c7-3596e4a729aa
-- title:
--   First Passage Linear Transport: loss Filtered odd Count rigidity
-- statement:
--   Loss-filtered sources in one half-open dyadic shell and one tag have one
--   common odd count.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L81-L152
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L81-L152

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.lossFiltered_oddCount_rigidity
    {M Y h y n₁ n₂ : ℕ} {D : ℚ}
    (hn₁ : n₁ ∈ lossFilteredTaggedFiber M Y h y D)
    (hn₂ : n₂ ∈ lossFilteredTaggedFiber M Y h y D)
    (hY : 0 < Y) (_hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    oddCount n₁ h = oddCount n₂ h := by sorry
