-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_card_real_le
-- name    : FirstPassageLinearTransport.generatedFirstBadSources_card_real_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:28.163496+00:00
-- url     : https://prove2.me/theorems/9aa8ed54-1cfe-5c05-979e-a6294ed9d837
-- title:
--   First Passage Linear Transport: generated First Bad Sources card real le
-- statement:
--   Real-valued form of the exact rank-by-rank generated first-bad transport
--   bound.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L24-L34
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L24-L34

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.generatedFirstBadSources_card_real_le
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q * ((landingBad q t).card : ℝ) := by sorry
