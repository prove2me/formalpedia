-- Prove2me | Theorems.Thm_A166944Research_a166944_target_of_travel
-- name    : A166944Research.a166944_target_of_travel
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-15T00:11:12.574344+00:00
-- url     : https://prove2.me/theorems/69e77e60-6b7e-42fc-86ab-64e849a4276c
-- title:
--   The A166944 target follows from the travel bound at record 45895573
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944 with first differences $d_n$ and offset $D_n=a_n-n$, and let $M$ be a difference record. Write $(sf,Cf)$ for the terminal state of the canonical replay started at $(M+2,\,2M-2)$, that is, the replay that jumps from each state to the next index at which the recursion's `gcd` is nontrivial.
--
--   Assume the **travel bound**: for every record $M\ge 45895573$ already known to be the greater member of a twin-prime pair,
--
--   $$
--   2\,\bigl(sf-(M+2)\bigr)\;\le\;M .
--   $$
--
--   The theorem concludes the **A166944 target**:
--
--   $$
--   \forall R\in\mathbb{N},\qquad 5<R \;\wedge\; \bigl(R \text{ is a difference record}\bigr) \;\Longrightarrow\; R \text{ and } R-2 \text{ are both prime}.
--   $$
--
--   So the conjecture follows from the travel bound. This is the reduction step of the project's attack: everything else has been discharged, either by proof or by finite computation.
--
--   The argument is an induction on records. Records are known to be unbounded, so the induction is well founded along the record sequence. For a record $R$ below the finite threshold $45895573$ the conclusion is a kernel-checked finite statement, obtained by replaying the recurrence and testing the two candidate factors. For a larger $R$ the previous record $M$ is itself a record above the threshold, so by induction it is a twin-prime greater member; the travel bound then controls the canonical replay started at $M$, and the termination alternative of that replay forces the next record to be $R=M'$ with both $M'$ and $M'-2$ free of proper divisors. That last step is where the travel bound is consumed: without it the replay could travel far enough to produce a value that is not forced in this way.
--
--   The threshold $45895573$ is not a mathematical constant: it is where the project's explicit replay certificates stop. Below it the statement is checked directly, so the theorem is unconditional there and the travel hypothesis is only used above it.
--
--   **Formalization Note** The hypothesis is stated in expanded form rather than through a named predicate so that this theorem can be read against the sibling `a166944_travel_bound_from_45895573` directly; the two are the same proposition. The condition `IsGreaterTwinPrime M` is carried in the travel hypothesis because the induction only needs travel after a record whose twin-primality is already established, which is what keeps the argument non-circular.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/TravelTarget.lean (target_of_twin_travel_from_fifty_million) and A166944/VerifiedFiftyMillionBridge.lean (the fifty-million bridge that supplies the threshold).

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_target_of_travel
    (htravel : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M) :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R := by
  sorry

end A166944Research
