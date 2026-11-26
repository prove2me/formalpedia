-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellPrefixMultiplicativeHit_crosses
-- name    : FirstPassageLinearTransport.shellPrefixMultiplicativeHit_crosses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:54.603102+00:00
-- url     : https://prove2.me/theorems/0d24b223-7149-5d45-8a6c-1f46cf994778
-- title:
--   First Passage Linear Transport: shell Prefix Multiplicative Hit crosses
-- statement:
--   The First Passage Linear Transport construction uses the shell Prefix Multiplicative Hit crosses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L132-L155
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L132-L155

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.shellPrefixMultiplicativeHit_crosses
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ}
    {n : {n : ℕ // n ∈ dyadicShell M}}
    (hn : n ∈ shellPrefixMultiplicativeHit M h hhM u) :
    crossesMultiplicativeFrom u h 1 (boolParityWord h n.1) := by sorry
