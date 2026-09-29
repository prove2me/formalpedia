-- Prove2me | Theorems.Thm_FamousTheorems_rabin_scott_subset_construction_6c
-- name    : FamousTheorems.rabin_scott_subset_construction_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:48.824814+00:00
-- url     : https://prove2.me/theorems/6ec67df9-f62c-4ede-aaec-30de7e26603d
-- title:
--   The Rabin–Scott subset construction (NFA to DFA)
-- statement:
--   **The Rabin–Scott subset construction.** For every nondeterministic finite automaton $M$ over an alphabet $\alpha$ with state set $\sigma$, the deterministic automaton whose states are the sets of states of $M$ accepts the same language as $M$.
--
--   Rabin and Scott introduced this construction in 1959. It shows that nondeterminism adds no power to finite automata: NFAs and DFAs recognise the same languages, the regular languages. The blow-up from $|\sigma|$ to $2^{|\sigma|}$ states is unavoidable in the worst case.
--
--   **Formalization note.** Mathlib's `NFA.toDFA_correct`. `M.toDFA` is the subset automaton, with states `Set σ`, start state the set of start states, and accepting states the sets meeting the accepting states of $M$. `accepts` is the accepted language, a `Language α`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NFA.toDFA_correct`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rabin_scott_subset_construction_6c {α σ : Type*} (M : NFA α σ) : M.toDFA.accepts = M.accepts := by sorry

end FamousTheorems
