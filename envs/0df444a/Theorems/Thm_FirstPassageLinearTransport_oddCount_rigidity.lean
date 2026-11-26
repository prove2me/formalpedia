-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_rigidity
-- name    : FirstPassageLinearTransport.oddCount_rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:46.692741+00:00
-- url     : https://prove2.me/theorems/87558e7e-a689-419d-aa85-680be86ef366
-- title:
--   First Passage Linear Transport: odd Count rigidity
-- statement:
--   A nonempty tagged fiber in one half-open dyadic shell has one
--   odd count.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L302-L338
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L302-L338

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.oddCount_rigidity {M Y h y n₁ n₂ : ℕ}
    (hn₁ : n₁ ∈ dyadicShell M) (hn₂ : n₂ ∈ dyadicShell M)
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hfp₁ : IsFirstPassage Y n₁ h) (hy₁ : orbit h n₁ = y)
    (hfp₂ : IsFirstPassage Y n₂ h) (hy₂ : orbit h n₂ = y) :
    oddCount n₁ h = oddCount n₂ h := by sorry
