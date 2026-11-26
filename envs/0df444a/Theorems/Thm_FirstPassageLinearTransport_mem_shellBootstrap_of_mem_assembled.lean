-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_shellBootstrap_of_mem_assembled
-- name    : FirstPassageLinearTransport.mem_shellBootstrap_of_mem_assembled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:44:06.899991+00:00
-- url     : https://prove2.me/theorems/734e7e4d-2537-4904-9911-2aa67155f887
-- title:
--   First Passage Linear Transport: mem shell Bootstrap of mem assembled
-- statement:
--   The First Passage Linear Transport construction uses the mem shell Bootstrap of mem assembled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean#L34-L38
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean#L34-L38

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.mem_shellBootstrap_of_mem_assembled
    {r eta : ℝ} (p : StageSetup r eta) {omega : ℝ} {n : ℕ}
    (hn : n ∈ assembledBootstrap p omega) :
    n ∈ bootstrapSet p (stageCount omega (Nat.log 2 n)) := by sorry
