-- Prove2me | Theorems.Thm_A166944Research_a166944_travel_bound_from_45895573
-- name    : A166944Research.a166944_travel_bound_from_45895573
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-15T00:10:10.57421+00:00
-- url     : https://prove2.me/theorems/3e21b815-5af9-4846-b9e6-0ddf81af2df3
-- title:
--   The A166944 canonical travel bound from record 45895573 onward
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n=a_n-a_{n-1}$ its first differences, and $D_n=a_n-n$ its offset from the identity. Let $M$ be a **difference record** whose value is already known to be the greater member of a twin-prime pair, so that $d_{M+2}=M$; the canonical replay of the moving-horizon dynamics then starts at the state
--
--   $$
--   (s,C)=\bigl(M+2,\;2M-2\bigr),
--   $$
--
--   and follows the recurrence by jumping from each state to the next index at which a `gcd` in the recursion is nontrivial. Write $(sf,Cf)$ for the state at which that replay terminates.
--
--   The theorem bounds how far the replay travels before it terminates:
--
--   $$
--   2\,\bigl(sf-(M+2)\bigr)\;\le\;M .
--   $$
--
--   In words: the terminal index exceeds the starting index by at most half the record value. Equivalently, writing $sf=M+2+t$ for a travel length $t$, the bound is $2t\le M$.
--
--   This is the last remaining ingredient for the A166944 conjecture. The index and twin-primality conclusions are already reduced to it: the project's `REACH.md` records that the finite replay certificates reach record $11{,}751{,}795{,}061$, and that everything beyond them follows from this single inequality. Under $M+2\le sf$ the inequality is *exactly* the index cap $2\,sf\le 3M+4$, so proving either form is the same task.
--
--   The statement is stated as a bound on the replay rather than on the recurrence, because the replay is what the existing theory controls: the project proves a per-step increment of at least two (`CountFromIndex`), a per-step gap of at most twice the record (`GapBound`), and that the reservoir coordinate at the exit is determined by the accumulated excess (`BIntegrate`). What none of them supplies is a bound on the *number* of steps, and that is what this inequality encodes: the count $p$ satisfies $2p\le B_{sf}+sf-2-(2M-2)$, so a bound on the travel is a bound on the count.
--
--   The verified certificates show the bound holds with room to spare: at $M=45{,}895{,}573$ the observed travel is $37$ events against an allowance of $977$, a factor of about $26$. The margin grows with $M$, which is why a finite check cannot settle the statement and a uniform argument is needed.
--
--   **Formalization Note** The quantifier over $M\ge 45895573$ is the lower bound at which the finite certificates stop; below it the bound is already proved by explicit replay. `IsGreaterTwinPrime M` is carried because the route to this point is an induction that only needs travel after a record already known to be a twin prime; this is how the project avoids circularity. `IsAttainedPreviousMaximum M sf` says every difference up to the terminal index is at most $M$, which is what makes the replay 'capped'.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). The reduction is machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/TravelTarget.lean (def TwinPrimeTravelBoundFrom, theorem target_of_twin_travel_from_fifty_million), and the obstruction is documented in REACH.md and GATE_MAP.md.

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_travel_bound_from_45895573 :
    ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M := by
  sorry

end A166944Research
