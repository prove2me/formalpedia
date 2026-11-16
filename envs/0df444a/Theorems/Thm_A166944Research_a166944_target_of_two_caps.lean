-- Prove2me | Theorems.Thm_A166944Research_a166944_target_of_two_caps
-- name    : A166944Research.a166944_target_of_two_caps
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-15T06:19:41.082524+00:00
-- url     : https://prove2.me/theorems/38c6e3ed-b050-4927-b50d-1dad40e58802
-- title:
--   The A166944 target follows from two caps, each weaker than the travel bound
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944 and $d_n = a_n - a_{n-1}$ its first differences. Let $M$ be a difference record whose value is known to be the greater member of a twin-prime pair, so that $d_{M+2} = M$; the **canonical replay** starts at the state $(M+2,\;2M-2)$ and jumps to the next index at which the recursion's `gcd` is nontrivial. Write $(sf, Cf)$ for the state where it terminates.
--
--   Assume the replay satisfies two caps, for every record $M \ge 45895573$ already known to be a greater twin prime:
--
--   $$Cf \;\le\; 3M+4, \qquad 4\,sf \;\le\; 7M - 1 .$$
--
--   Then the **A166944 conjecture** holds: every difference record above $5$ is the greater member of a twin-prime pair.
--
--   ## Why two caps rather than one
--
--   The development previously carried a single hypothesis, the **travel bound**
--
--   $$2\,\bigl(sf-(M+2)\bigr) \le M, \qquad \text{equivalently} \qquad sf \le \tfrac32 M + 2 ,$$
--
--   and a dozen independent routes were recorded as all converging on it. That target was too strong. The only place the travel bound is consumed is a step that determines the next record from the replay, and measuring what its arithmetic actually needs shows it tolerates $sf$ up to $7M/4$: the relaxation is $M/4$, about $11.5$ million at $M = 45895573$.
--
--   So the pair of caps is **strictly easier** than the travel bound while sufficing for the same conclusion. That it is genuinely weaker, not a restatement, is witnessed: at $M = 45895573$ the pair $(sf, Cf) = (80317252,\,137686723)$ satisfies both caps and violates the travel bound.
--
--   There is also a structural gain. The replay's case analysis has two branches, and the branch where the replay crosses the record is discharged by an existing theorem about horizon growth using only the first cap. Only the quiet branch consumes the second.
--
--   ## Where it stands
--
--   Neither cap is proved for all $M$; both are uniform statements about the terminal state of a canonical replay, and the development's kernel-verified certificates reach record $11{,}751{,}795{,}061$ and no further. What this theorem establishes is that those two statements, rather than the stronger travel bound, are what stand between the finite certificates and the conjecture.
--
--   **Formalization Note** The lower bound $45895573$ is where the explicit replay certificates stop; below it both caps are discharged by replay. `IsGreaterTwinPrime M` is carried because the argument is an induction that only needs the caps after a record already known to be a twin prime, which is how circularity is avoided. The two hypotheses are stated separately rather than as a conjunction so that each can be attacked on its own.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). Machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/TwoCapGate.lean proves the consumer needs only these caps, A166944/TwoCapTarget.lean carries it to the top.

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_target_of_two_caps
    (hA : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4)
    (hB : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1) :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R := by
  sorry

end A166944Research
