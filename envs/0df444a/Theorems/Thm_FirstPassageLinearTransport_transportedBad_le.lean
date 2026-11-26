-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_transportedBad_le
-- name    : FirstPassageLinearTransport.transportedBad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:22.924691+00:00
-- url     : https://prove2.me/theorems/5a016078-aea3-5eea-84db-e3dd04dfcbbb
-- title:
--   First Passage Linear Transport: transported Bad le
-- statement:
--   The transported part of a failed shell pullback, with the target density
--   and floor loss already inserted.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L318-L379
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L318-L379

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.transportedBad_le {r eta C D : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    {M : ℕ} (hM : p.M0 ≤ M) :
    ((transportedSources M (targetScale r M) M
      (badTarget S (targetScale r M))).card : ℝ) ≤
      5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        Real.exp (-(r * D * M * Real.log 2)) := by sorry
