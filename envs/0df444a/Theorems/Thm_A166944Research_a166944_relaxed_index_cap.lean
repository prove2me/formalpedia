-- Prove2me | Theorems.Thm_A166944Research_a166944_relaxed_index_cap
-- name    : A166944Research.a166944_relaxed_index_cap
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-15T06:16:59.390212+00:00
-- url     : https://prove2.me/theorems/9f6a4ebb-6673-4482-9256-07fd9175a088
-- title:
--   The A166944 canonical replay satisfies a relaxed index cap, and this cap replaces the travel bound
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. Let $M$ be a difference record whose value is already known to be the greater member of a twin-prime pair, so that $d_{M+2} = M$; the **canonical replay** of the moving-horizon dynamics then starts at the state $(M+2,\;2M-2)$ and jumps from each state to the next index at which the recursion's `gcd` is nontrivial. Write $(sf,Cf)$ for the state at which that replay terminates.
--
--   This theorem bounds the terminal index:
--
--   $$4\,sf \;\le\; 7M - 1 .$$
--
--   In words, $sf$ is at most $7M/4$, or about $1.75M$.
--
--   ## Why this and not the stronger bound
--
--   The development has carried the **travel bound**
--
--   $$2\,\bigl(sf-(M+2)\bigr)\;\le\;M,$$
--
--   equivalently $sf \le 3M/2 + 2$, as its single stated obstruction for some time, and a dozen independent routes were recorded as all ending there. That framing was too strong. The only consumer of the travel bound is a step that decides the next record from the replay, and measuring what its arithmetic actually needs shows it tolerates $sf$ up to $7M/4$: the relaxation is $M/4$, which at the threshold $45895573$ is about $11.5$ million.
--
--   So this statement is **strictly easier** than the travel bound while being sufficient for the same conclusions. The evidence that it is genuinely weaker, rather than a restatement, is a witnessed pair at $M = 45895573$ with $sf = 80317252$ and $Cf = 137686723$: it satisfies $4\,sf \le 7M-1$ and $Cf \le 3M+4$ while violating the travel bound. Hence the relaxed cap does not imply the old one, and a proof of this statement would not be a restatement of it either.
--
--   ## Role in the development
--
--   The companion hypothesis $Cf \le 3M + 4$ is separately available and is not part of this statement. Together the two caps replace the travel bound in the induction that derives the index theorem and the twin-primality of records, so this single inequality is what stands between the finite certificates -- kernel-verified through record $11{,}751{,}795{,}061$ -- and the A166944 conjecture, and through it the Twin Prime Conjecture.
--
--   One structural gain is worth recording: the case analysis has two branches, and the branch where the replay crosses the record no longer depends on this cap at all. It is discharged by an existing theorem about horizon growth. Only the quiet branch consumes the bound stated here.
--
--   **Formalization Note** The quantifier over $M \ge 45895573$ is the lower bound at which the finite certificates stop; below it the statement is already proved by explicit replay. `IsGreaterTwinPrime M` is carried because the route to this point is an induction that only needs the bound after a record already known to be a twin prime, which is how the development avoids circularity. The constant $7$ in $4\,sf \le 7M-1$ is optimal in the sense that $4\,sf \le 7M$ is false for the arithmetic in question, while $4\,sf \le 7M-1$ is exactly what the proof needs.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). The reduction and the relaxation are machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/TwoCapGate.lean proves that the consumer needs only this cap, and A166944/TwoCapTarget.lean carries the relaxation to the top of the development.

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_relaxed_index_cap :
    ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1 := by
  sorry

end A166944Research
