-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_card_le
-- name    : FirstPassageLinearTransport.generatedFirstBadSources_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:02.084369+00:00
-- url     : https://prove2.me/theorems/e47cbcc1-7475-4f8b-9618-743d6c3eab7d
-- title:
--   First Passage Linear Transport: generated First Bad Sources card le
-- statement:
--   The First Passage Linear Transport construction uses the generated First Bad Sources card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L203-L219
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L203-L219

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.generatedFirstBadSources_card_le
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((generatedFirstBadSources M L U H r t).card : ℚ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by sorry
