-- Prove2me | Theorems.Thm_DetDLP_divisor_bisection_and_btn_scale
-- name    : DetDLP.divisor_bisection_and_btn_scale
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T14:02:51.35721+00:00
-- url     : https://prove2.me/theorems/dedd02df-bf41-450c-a8d4-fa964b9f4ab3
-- title:
--   Proper-Divisor Soundness of Minimum Factor and Interval-Bisection Decision Invariant
-- statement:
--   Establishes the mathematical soundness of the interval-bisection divisor search in Proposition 2.6:
--
--   1. For every composite integer $N \ge 2$, the least prime factor $d^* = \mathrm{minFac}(N)$ satisfies $2 \le d^* < N$ and $d^* \mid N$;
--   2. For any interval $[L, R)$ and midpoint $M \in [L, R]$, the divisor count $C(a, b) = |\{d \in [a, b) : d \mid N\}|$ is additive ($C(L, R) = C(L, M) + C(M, R)$), and whenever $2 \le L \le d^* < R$, the left-half count $C(L, M)$ uniquely decides which half contains $d^*$: $$d^* < M \iff C(L, M) > 0, \qquad M \le d^* \iff C(L, M) = 0.$$
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3 Proposition 2.6 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

/-- Mathematical soundness of the Proposition 2.6 interval-bisection divisor search (Section 2.3,
pp. 10–11):
1. Choosing `f := Nat.minFac`, for every composite `N ≥ 2` (`¬ N.Prime`), `f N` is a proper
   divisor of `N` (`2 ≤ N.minFac ∧ N.minFac < N ∧ N.minFac ∣ N`).
2. Additivity and binary-search decision invariant for interval divisor counts
   `C(a, b) = |{d ∈ [a, b) : d ∣ N}|`: for any `2 ≤ L ≤ M ≤ R` with `L ≤ N.minFac < R`,
   `C(L, R) = C(L, M) + C(M, R)`, `N.minFac < M ↔ 0 < C(L, M)`, and
   `M ≤ N.minFac ↔ C(L, M) = 0`. -/
theorem divisor_bisection_and_btn_scale :
    (∀ N : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ N.minFac ∧ N.minFac < N ∧ N.minFac ∣ N) ∧
    (∀ N L M R : ℕ, L ≤ M → M ≤ R →
      ((Finset.Ico L R).filter (fun d => d ∣ N)).card =
        ((Finset.Ico L M).filter (fun d => d ∣ N)).card +
        ((Finset.Ico M R).filter (fun d => d ∣ N)).card) ∧
    (∀ N L M R : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ L → L ≤ N.minFac → N.minFac < R → L ≤ M → M ≤ R →
      (N.minFac < M ↔ 0 < ((Finset.Ico L M).filter (fun d => d ∣ N)).card) ∧
      (M ≤ N.minFac ↔ ((Finset.Ico L M).filter (fun d => d ∣ N)).card = 0)) := by
  sorry

end DetDLP
