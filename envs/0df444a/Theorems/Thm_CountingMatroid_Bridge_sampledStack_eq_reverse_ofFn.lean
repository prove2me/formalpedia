-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_sampledStack_eq_reverse_ofFn
-- name    : CountingMatroid.Bridge.sampledStack_eq_reverse_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:49:02.662205+00:00
-- url     : https://prove2.me/theorems/cf12c104-e838-49ad-8694-b8e029089743
-- title:
--   The sampler stack is the reversed indexed bit list
-- statement:
--   For every finite number of sampler rounds, the recursively accumulated sample stack is exactly the reverse of the list of sampled bits indexed by the round number. This identity connects the machine’s stack order to the estimator’s finite-list input.
-- source:
--   Lean 4.33.1 helper lemma for exact finite-bit sampler semantics.

import Definitions.Def_CountingMatroidBridgeBalancedSampler

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem CountingMatroid.Bridge.sampledStack_eq_reverse_ofFn {K : ℕ} (bits : ℕ → Bool) :
    sampledStack bits K =
      (List.ofFn (fun i : Fin K => bits (3 * i.val + 1))).reverse := by
  sorry
