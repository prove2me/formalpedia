-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_endpoint_lt_start
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_lt_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:37.104817+00:00
-- url     : https://prove2.me/theorems/75793d6f-f1bf-5d7a-bbbc-0ef70ae130a5
-- title:
--   Timeout Recertification Run: endpoint lt start
-- statement:
--   The Timeout Recertification Run construction uses the endpoint lt start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L65-L73
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L65-L73

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_lt_start
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M) : orbit elapsed n < n := by sorry
