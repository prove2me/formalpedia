-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_assembleDyadic
-- name    : FirstPassageLinearTransport.naturalDensityOne_assembleDyadic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:14.423657+00:00
-- url     : https://prove2.me/theorems/d5b198df-4783-4dfe-992e-e9eb73f59832
-- title:
--   First Passage Linear Transport: natural Density One assemble Dyadic
-- statement:
--   Varying-rate dyadic-shell lemma: shellwise exceptional ratios tending
--   to zero assemble to a natural-density-one set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L110-L249
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L110-L249

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.naturalDensityOne_assembleDyadic
    (S : ℕ → Set ℕ)
    (hvanish :
      Filter.Tendsto
        (fun M => shellExceptionalRatio (S M) M)
        Filter.atTop (nhds 0)) :
    NaturalDensityOne (assembleDyadic S) := by sorry
