-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBad_pullback_subset
-- name    : FirstPassageLinearTransport.shellBad_pullback_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:09:00.241911+00:00
-- url     : https://prove2.me/theorems/a485ac36-26f6-52c3-a5ae-79d4cc579d66
-- title:
--   First Passage Linear Transport: shell Bad pullback subset
-- statement:
--   Exact shell decomposition: a failed pullback source is either outside
--   the retained window or belongs to the already-formalized first-passage
--   transport set for the bad target cells.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L208-L239
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L208-L239

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shellBad_pullback_subset {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) {M : ℕ} (hM : p.M0 ≤ M) :
    shellBad (firstPassagePullback p S) M ⊆
      shellBad (extendedWindow p) M ∪
        transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M)) := by sorry
