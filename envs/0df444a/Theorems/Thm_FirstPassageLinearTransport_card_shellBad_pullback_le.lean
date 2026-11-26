-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellBad_pullback_le
-- name    : FirstPassageLinearTransport.card_shellBad_pullback_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:09:19.622661+00:00
-- url     : https://prove2.me/theorems/2b45cc6b-af9f-507e-9022-145945c4b461
-- title:
--   First Passage Linear Transport: card shell Bad pullback le
-- statement:
--   The First Passage Linear Transport construction uses the card shell Bad pullback le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L241-L252
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L241-L252

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_shellBad_pullback_le {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) {M : ℕ} (hM : p.M0 ≤ M) :
    (shellBad (firstPassagePullback p S) M).card ≤
      (shellBad (extendedWindow p) M).card +
        (transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M))).card := by sorry
