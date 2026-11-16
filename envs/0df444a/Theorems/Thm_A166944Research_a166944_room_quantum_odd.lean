-- Prove2me | Theorems.Thm_A166944Research_a166944_room_quantum_odd
-- name    : A166944Research.a166944_room_quantum_odd
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-15T10:26:35.437943+00:00
-- url     : https://prove2.me/theorems/3f6d1b1a-6698-4d0a-a367-71e54dc0770c
-- title:
--   The A166944 odd-hit shifted room is $3e$, or at least one quantum $5e$ above it
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. A **moving-horizon step** relates a state $(s, C)$ with $C = D_s$ to the next index $r > s$ at which the recursion's `gcd` is non-trivial:
--   $$d_r > 1, \qquad d_j = 1 \ \text{ for all } s < j < r, \qquad C' = D_r ,$$
--   with the guard $C + 2 \le C'$. Write $e := d_r$ for the **event value**.
--
--   ## The statement
--
--   At an **odd** hit the quotient normal form for the shifted room reads
--   $$C' - r + 4 \;=\; e\,(q+1)$$
--   with $q$ **even** and $q \ge 2$. Hence
--
--   $$C' - r + 4 = 3e \qquad \text{or} \qquad 5e \;\le\; C' - r + 4 .$$
--
--   This is the same phenomenon as the even branch, translated by the shift of $4$ that the odd step law carries: the minimum is $3e$ and the next reachable quantum is $5e$, with nothing in between. The pair of parity statements together is the exact quantisation of the room.
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

theorem a166944_room_quantum_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    C' - r + 4 = 3 * d r ∨ 5 * d r ≤ C' - r + 4 := by
  sorry

end A166944Research
