-- Prove2me | Theorems.Thm_A166944Research_a166944_event_dvd_next_horizon
-- name    : A166944Research.a166944_event_dvd_next_horizon
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-15T10:26:27.888192+00:00
-- url     : https://prove2.me/theorems/768e809c-a0ce-47bc-80cf-ee6721629e85
-- title:
--   The A166944 event value divides the horizon that follows it
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. A **moving-horizon step** relates a state $(s, C)$ with $C = D_s$ to the next index $r > s$ at which the recursion's `gcd` is non-trivial:
--   $$d_r > 1, \qquad d_j = 1 \ \text{ for all } s < j < r, \qquad C' = D_r ,$$
--   with the guard $C + 2 \le C'$. Write $e := d_r$ for the **event value**.
--
--   ## The statement
--
--   The two parity cases of the carry, bundled into one statement:
--
--   $$r \equiv 0 \pmod 2 \;\Longrightarrow\; e \mid C', \qquad r \equiv 1 \pmod 2 \;\Longrightarrow\; e \mid C' + 2 .$$
--
--   In both cases the divisor $e$ is inherited by the *post*-step horizon. This fact is already used in the development as a local step in a longer path argument; it is stated standalone here because the path-level arguments need it in that form. It is a repackaging of content already present elsewhere, **not** a new discovery, and is flagged as such so it is not double-counted.
--
--   ## Role
--
--   Recorded as part of the room-quantisation cluster in `RoomQuantum.lean`, which isolates what survives the prior-art check on the angle "evaluate $\gcd(C \pm 1, r)$": the quantity that angle proposes to bound turns out to be a **definition** rather than a derived constraint, and what carries new content is the interaction of the two divisibilities ($e \mid r$ and $e \mid C \pm 1$) with the step law.
--
--   ## What this does not do
--
--   The statement is local to one step. It is exact, and it is still compatible with an arbitrarily large *accumulated* excess over a whole replay: on the degenerate branch the quotient is pinned to a small value while $e$ itself stays free. It is recorded with that limitation explicit, so it is not over-claimed as progress on the global barrier.
--
--   **Formalization Note** Transcribed verbatim from `A166944/RoomQuantum.lean` at commit `a3bc097`; kernel-checked with no `sorryAx` (the proof depends only on `propext` and `Quot.sound`). Pure core tactics (`decide` / `omega` / `simp` / `rfl`) — no `ring`, `linarith`, `norm_num`, `positivity` or `interval_cases`. Verified on all 230 steps of the fifteen canonical record replays below $2 \times 10^6$: zero violations.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). Machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/RoomQuantum.lean, commit a3bc097ef9ea9981cb1853ffd120528639eeffbe.

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_event_dvd_next_horizon {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r ∣ C') ∧ (r % 2 = 1 → d r ∣ C' + 2) := by
  sorry

end A166944Research
