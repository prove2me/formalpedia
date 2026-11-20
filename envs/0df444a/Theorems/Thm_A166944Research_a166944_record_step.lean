-- Prove2me | Theorems.Thm_A166944Research_a166944_record_step
-- name    : A166944Research.a166944_record_step
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-19T06:17:17.78141+00:00
-- url     : https://prove2.me/theorems/8d768d83-7f55-4e11-9fbe-51d778286241
-- title:
--   The A166944 record step: a certified record passes twin-primality forward
-- statement:
--   Let $a$ be the OEIS A166944 recurrence. Write $\operatorname{NoProperFactor}(N)$ for: no integer $f$ with $2\le f<N$ divides $N$.
--
--   Suppose $M>5$ is a difference record whose value is the greater member of a twin-prime pair, and suppose a canonical replay from $M$ produces the next record: the value $C+1$ is attained before $C+2$, it occurs at index $C+3$, and neither $C-1$ nor $C+1$ has a proper divisor. Then $C+1$ is also the greater member of a twin-prime pair:
--
--   $$\operatorname{IsGreaterTwinPrime}(C+1).$$
--
--   This is the induction step that lets the record sequence be read forward. The terminal leaves certify the *next* record from a given one; the parent statement concerns *every* record. Composing them requires exactly this step: that the next record inherits the twin-prime property from the certificates the replay produced.
--
--   The mathematical content is a change of viewpoint. The certificate at the next record is that $C+1$ and $C-1$ have no proper divisor, i.e. that $(C+1)-2$ and $C+1$ are both prime. That is precisely the greater-twin-prime condition for $C+1$, written in the divisor form the replay can supply. So the step is where the divisor-form certificate is converted into the primality statement the parent is phrased in.
--
--   **Why it is not a formality.** The replay's certificate is *absence of a divisor*, not primality, and the conversion needs the horizon bound $N<(\rho+1)^2$ together with the step `no_proper_factor_of_no_small_factor`. It also needs the record to be *attained* before the horizon, which `IsAttainedPreviousMaximum M (C+2)` supplies; without it the value $C+1$ could be an isolated spike rather than a running maximum.
-- source:
--   Derived within this development; the Mathlib-side original is QuietReturn.canonical_next_record_factors_of_short_travel composed with the factor-to-primality step. See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_record_core
import Definitions.Def_a166944_moving_horizon
import Definitions.Def_a166944_B
import Definitions.Def_a166944_factor_layer

open A166944Research

namespace A166944Research

theorem a166944_record_step {M C : Nat}
    (hT : IsGreaterTwinPrime M) (hM : 5 < M)
    (hnext : IsAttainedPreviousMaximum M (C + 2))
    (hd : d (C + 3) = C + 1)
    (hminus : NoProperFactor (C - 1)) (hplus : NoProperFactor (C + 1)) :
    IsGreaterTwinPrime (C + 1) := by
  sorry

end A166944Research
