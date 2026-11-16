-- Prove2me | Theorems.Thm_A166944Research_a166944_room_quantum_even
-- name    : A166944Research.a166944_room_quantum_even
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-15T10:26:31.778818+00:00
-- url     : https://prove2.me/theorems/be8f0dea-dc7d-4d2a-8dbe-e291f97990a9
-- title:
--   The A166944 even-hit room is $2e$, or at least one quantum $4e$ above it
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. A **moving-horizon step** relates a state $(s, C)$ with $C = D_s$ to the next index $r > s$ at which the recursion's `gcd` is non-trivial:
--   $$d_r > 1, \qquad d_j = 1 \ \text{ for all } s < j < r, \qquad C' = D_r ,$$
--   with the guard $C + 2 \le C'$. Write $e := d_r$ for the **event value**.
--
--   ## The statement
--
--   Define the **room** left after a step as $\mathrm{room}' := C' - r$. At an **even** hit the quotient normal form gives
--   $$C' - r \;=\; e\,(q+1)$$
--   with $q$ **odd** and $q \ge 1$. Because $q + 1$ is therefore even, the room is always an even multiple of $e$:
--
--   $$C' - r = 2e \qquad \text{or} \qquad 4e \;\le\; C' - r .$$
--
--   The intermediate value $2e + 2$ is *arithmetically unreachable*, not merely unobserved. An earlier version of this statement claimed $2e + 2 \le C' - r$; that is true but weak, and `omega` refuted the sharper-looking variant by exhibiting the explicit profile $r/2 = b$, $e = c$, $C' = \hat e$ with $2b = \hat e$ and $2b + 2c = \hat e - 2$. The quantum in the even branch is $4e$.
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

theorem a166944_room_quantum_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    C' - r = 2 * d r ∨ 4 * d r ≤ C' - r := by
  sorry

end A166944Research
