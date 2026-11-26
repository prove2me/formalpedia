-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_endpointEntropyRate
-- name    : FirstPassageLinearTransport.tendsto_endpointEntropyRate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:40.680805+00:00
-- url     : https://prove2.me/theorems/9843f537-c699-42ed-8a5c-7e581ffb80b9
-- title:
--   First Passage Linear Transport: tendsto endpoint Entropy Rate
-- statement:
--   The First Passage Linear Transport construction uses the tendsto endpoint Entropy Rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedPolylogParameters.lean#L146-L159
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedPolylogParameters.lean#L146-L159

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_endpointEntropyRate :
    Tendsto
      (fun n : ℕ =>
        adjustableEntropyRate (endpointLambda n) (endpointTolerance n))
      atTop (nhds firstPassageEndpointRate) := by sorry
