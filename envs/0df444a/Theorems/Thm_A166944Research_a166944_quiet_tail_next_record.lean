-- Prove2me | Theorems.Thm_A166944Research_a166944_quiet_tail_next_record
-- name    : A166944Research.a166944_quiet_tail_next_record
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-19T04:53:38.789389+00:00
-- url     : https://prove2.me/theorems/ef7c1768-0694-45bd-b19c-f75a7d575900
-- title:
--   A quiet tail at a canonical horizon produces the next A166944 record
-- statement:
--   Let $a$ be the OEIS A166944 recurrence, $d_n = a_n - a_{n-1}$ its first differences, and $M$ a difference record with $M\ge 968$ and $d_{M+2}=M$. Suppose $M$ is an attained running maximum of $d$ up to the terminal index $s_f$, and that from $s_f$ onward through the horizon $C_f$ every increment is a unit: $d_j=1$ for all $s_f<j\le C_f$. Assume also $C_f\ge 2M-2$.
--
--   Then the value $C_f+1$ is itself a difference record, it is attained before $C_f+2$, and it occurs at index $C_f+3$:
--
--   $$M < C_f+1, \qquad \max_{2\le j\le C_f+2} d_j = C_f+1, \qquad d_{C_f+3} = C_f+1.$$
--
--   In words: the terminal horizon of a capped canonical replay determines the *next* record exactly, one step beyond the point where the replay stopped. This is the structural reason the record sequence can be read forward from any certified start, and it is the first half of the mechanism that produces the twin-prime certificates at the next record: the value is at index $C_f+3$, and its neighbours $C_f+1$ and $C_f+3$ are where the factor certificates attach.
--
--   The proof runs through the offset ledger. Quietness makes the offset $D_n=a_n-n$ constant across the tail, and the terminal identity $B_{C_f}=2$ (which follows from the same ledger) resets the recurrence at index $C_f+3$. The content of this statement is that the reset is unconditional once the tail is quiet: no further hypothesis on $M$ or on the arithmetic of $C_f\pm1$ is needed.
-- source:
--   Derived within this development; the Mathlib-side original is RecordReplay.canonical_quiet_return_next_record. See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_quiet_tail_next_record {M sf Cf : Nat}
    (hM : 968 ≤ M) (hF : 2 * M - 2 ≤ Cf)
    (hstate : IsMovingHorizonState sf Cf) (hfmax : IsAttainedPreviousMaximum M sf)
    (hquiet : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) :
    M < Cf + 1 ∧ IsAttainedPreviousMaximum M (Cf + 2) ∧ d (Cf + 3) = Cf + 1 := by
  sorry

end A166944Research
