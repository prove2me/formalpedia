-- Prove2me | Theorems.Thm_A166944Research_a166944_room_quantum
-- name    : A166944Research.a166944_room_quantum
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-15T10:14:59.581459+00:00
-- url     : https://prove2.me/theorems/efc4e465-8940-4cb1-b045-699520b4e350
-- title:
--   The A166944 room is quantised by the event value: the slack is not a continuum
-- statement:
--   The **moving-horizon replay** of the OEIS A166944 recurrence jumps from one *event* to the next, and each event leaves behind a quantity we call the **room**. The room was expected to be an arbitrary natural number above a minimum. This theorem says it is not: the room is **quantised by the event's own value**, and it may only land on the first lattice point or beyond the second.
--
--   ## Setup
--
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. A **moving-horizon step** relates a state $(s, C)$ with $C = D_s$ to the next index $r > s$ at which the recursion's `gcd` is non-trivial:
--   $$d_r > 1, \qquad d_j = 1 \ \text{ for all } s < j < r, \qquad C' = D_r,$$
--   where the step carries the guard $C + 2 \le C'$.
--
--   Write $e := d_r$ for the **event value** and define the *room* left after the step as
--   $$\mathrm{room}' \;:=\; C' - r .$$
--
--   ## The statement
--
--   For every moving-horizon step:
--
--   $$r \equiv 0 \pmod 2 \;\Longrightarrow\; \Bigl(\, C' - r = 2e \;\;\lor\;\; 4e \;\le\; C' - r \,\Bigr),$$
--   $$r \equiv 1 \pmod 2 \;\Longrightarrow\; \Bigl(\, C' - r + 4 = 3e \;\;\lor\;\; 5e \;\le\; C' - r + 4 \,\Bigr).$$
--
--   Equivalently: the parity of the hit index fixes a **minimum** room ($2e$, resp. $3e$ after a shift of $4$), and the room can never land strictly between that minimum and the **next quantum** ($4e$, resp. $5e$). The admissible values are exactly the two branches.
--
--   ## Why the gap is real
--
--   The mechanism is the quotient normal form. For an even hit one has
--   $$C' - r \;=\; e\,(q+1)$$
--   with $q$ **odd** and $q \ge 1$. Since $q + 1$ is therefore **even** and at least $2$, the room is always an even multiple of $e$: the value $2e + 2$ is *arithmetically unreachable*, not merely unobserved. The even branch's quantum is $4e$, **not** $2e + 2$ — an earlier version of this statement claimed $2e+2$ and `omega` refuted it, exhibiting the explicit profile $r/2 = b$, $e = c$, $C' = \hat e$ with $2b = \hat e$ and $2b + 2c = \hat e - 2$. The odd branch is the same phenomenon shifted by $4$: $C' - r + 4 = e(q+1)$ with $q$ even and $q \ge 2$, so the values are $3e$ or at least $5e$.
--
--   ## Role
--
--   This is the sharp form of the slack estimate `two_mul_increment_le_room_next`, and it is what a summation over a replay needs: knowing the room cannot sit just above its minimum is exactly the information that a bound on the accumulated excess would have to consume. It is a **local** statement — see the note below on what it does *not* give.
--
--   ## What this does not do
--
--   The dichotomy is exact and it is still compatible with an arbitrarily large accumulated excess. On the degenerate even branch ($C' - r = 2e$) the quotient $q$ is pinned to $1$, but $e$ itself is free; the odd branch's $q = 2$ case likewise leaves $e$ free. The local system therefore admits $\sum e_i$ far above $(3M-9)/8$; this is not a defect of the proof but a genuine limitation of the local structure, and it is recorded so the theorem is not over-claimed as progress on the global barrier.
--
--   **Formalization Note** Verbatim from `A166944/RoomQuantum.lean` at commit `a3bc097`, kernel-checked with no `sorryAx` (the proof depends only on `propext` and `Quot.sound`). The statement is the bundled two-parity form; `moving_horizon_room_quantum_even` and `moving_horizon_room_quantum_odd` are its two components. The companion divisibility results `moving_horizon_event_dvd_room_even` ($e \mid C' - r$) and `moving_horizon_event_dvd_room_odd` ($e \mid C' - r + 4$) expose the same quotient normal form as a divisibility statement. Verified on all 230 steps of the fifteen canonical record replays below $2 \times 10^6$: zero violations.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). Machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/RoomQuantum.lean, commit a3bc097ef9ea9981cb1853ffd120528639eeffbe.

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_room_quantum {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → C' - r = 2 * d r ∨ 4 * d r ≤ C' - r) ∧
      (r % 2 = 1 → C' - r + 4 = 3 * d r ∨ 5 * d r ≤ C' - r + 4) := by
  sorry

end A166944Research
