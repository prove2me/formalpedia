-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_assembledBootstrap_naturalDensityOne_of_vanish
-- name    : FirstPassageLinearTransport.assembledBootstrap_naturalDensityOne_of_vanish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:21:52.701695+00:00
-- url     : https://prove2.me/theorems/4c569d17-53ad-5b43-b2a7-ffcf2142c331
-- title:
--   First Passage Linear Transport: assembled Bootstrap natural Density One of vanish
-- statement:
--   The First Passage Linear Transport construction uses the assembled Bootstrap natural Density One of vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean#L26-L32
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean#L26-L32

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.assembledBootstrap_naturalDensityOne_of_vanish
    {r eta : ℝ} (p : StageSetup r eta) (omega : ℝ)
    (hvanish : Filter.Tendsto
      (fun M => shellExceptionalRatio (shellBootstrap p omega M) M)
      Filter.atTop (nhds 0)) :
    NaturalDensityOne (assembledBootstrap p omega) := by sorry
