-- Prove2me | Theorems.Thm_A166944Research_a166944_quiet_tail_no_small_factors
-- name    : A166944Research.a166944_quiet_tail_no_small_factors
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-19T04:53:40.946004+00:00
-- url     : https://prove2.me/theorems/ae9a5485-adda-49f9-813e-3bcf454e4196
-- title:
--   A long quiet A166944 tail certifies both twin factors
-- statement:
--   Let $a$ be the OEIS A166944 recurrence and $d_n=a_n-a_{n-1}$ its first differences. Suppose $(s_f, C_f)$ is a moving-horizon state and the tail is quiet: $d_j=1$ for every $s_f<j\le C_f$. If the tail is long compared with $\rho$, in the sense $2\rho < C_f-s_f$, then neither $C_f-1$ nor $C_f+1$ has any divisor in $[2,\rho]$:
--
--   $$\text{no } f \text{ with } 2\le f\le\rho \text{ divides } C_f-1, \qquad \text{no } f \text{ with } 2\le f\le\rho \text{ divides } C_f+1.$$
--
--   The mechanism is that a divisor is also a *position*. A factor $f$ of $C_f+1$ can be reflected across the horizon to the index $j = C_f+3-2f$, and a factor of $C_f-1$ to $j=C_f-1-f$; the bound $2\rho<C_f-s_f$ is exactly what keeps $j$ inside the quiet tail. At such an index the recurrence is forced to increment by exactly $1$, while the divisibility structure forces the increment to be a nontrivial gcd -- a contradiction. The parity split is what makes the reflection land on an index of the correct parity for the branch.
--
--   This is the step that converts quietness into coprimality at the horizon's two neighbours, which is in turn what makes the next difference record a twin prime. It is the only place in the terminal argument where the length of the quiet tail enters.
-- source:
--   Derived within this development; the Mathlib-side original is QuietReturn.quiet_return_no_small_factors (private there). See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_moving_horizon
import Definitions.Def_a166944_factor_layer

open A166944Research

namespace A166944Research

theorem a166944_quiet_tail_no_small_factors {sf Cf root : Nat}
    (hstate : IsMovingHorizonState sf Cf)
    (hquiet : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1)
    (hlong : 2 * root < Cf - sf) :
    NoSmallFactor (Cf - 1) root ∧ NoSmallFactor (Cf + 1) root := by
  sorry

end A166944Research
