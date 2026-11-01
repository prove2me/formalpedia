-- Prove2me | Theorems.Thm_AndOrSched_section_2_derandomize_alg2
-- name    : AndOrSched.section_2_derandomize_alg2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:11.52633+00:00
-- url     : https://prove2.me/theorems/43962457-534b-4a07-97e6-69414f6c15d1
-- title:
--   §2, p.10 — derandomizing Algorithm 2 (corrected: (5f) with $\tau_l\ge p_j$)
-- statement:
--   Let $\varepsilon'>0$ and let $x$ be a feasible solution of LP (5). Then the candidate set $\mathcal B(x)$ of values of $\beta$ satisfies
--   1. $\mathcal B(x)\subseteq(0,1]$;
--   2. $|\mathcal B(x)|\le n\cdot L+1$;
--   3. if $T\ge1$, then $L\le 2+(1+\varepsilon')\log T/\varepsilon'$, so the number of candidates is polynomial in the input size;
--   4. for every $\beta\in(0,1]$ some $\hat\beta\in\mathcal B(x)$ gives every job the same sort key as $\beta$.
--
--   Differences from the source:
--   - correction: (5f): x_jl ≥ 0 for l ∈ [L] with τ_{l−1} ≥ p_j (other variables absent) → x_jl ≥ 0 for all l ∈ [L], and x_jl = 0 when τ_l < p_j; reason: as printed LP (5) is infeasible for A = {a}, B = {b}, p_a = 2, p_b = 0, P(b) = {a}, E∧ = ∅, ε′ = 1/2 (τ = (1, 1, 1.5, 2.25), L = 3, no l has τ_{l−1} ≥ 2), although the instance has a feasible schedule; a job completing in (τ_{l−1}, τ_l] has p_j ≤ τ_l
--   - encoding: at most n·L β-schedules, "polynomially bounded in the input size" → an explicit candidate set of size ≤ n·L + 1 reaching every key vector, and L ≤ 2 + (1 + ε′) log T / ε′; reason: the constant and the polynomial bound are made explicit; the extra candidate 1 covers β above every breakpoint
--   - generalization: x̄ (an optimal solution) → x any feasible solution of LP (5); reason: the count uses only (5b) and nonnegativity
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.10, "We can derandomize Algorithm 2 similar to Lemma 2. … So the number of β-schedules is bounded from above by n · L which is polynomially bounded in the input size."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_horizon
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_cand
open scoped Classical NNReal

namespace AndOrSched

/-- §2, p.10 (Happach, Schulz, arXiv:2001.07011v1): "We can derandomize Algorithm 2 similar to Lemma 2. Interpret x̄ as a
preemptive schedule that assigns jobs to intervals. Note that each job is preempted at most once per
time interval (τl−1, τl]. So the number of β-schedules is bounded from above by n · L which is
polynomially bounded in the input size."

For `ε' > 0` and every feasible solution `x` of LP (5): the candidate set lies in `(0, 1]` and has at
most `n · L + 1` elements, `L ≤ 2 + (1 + ε') log T / ε'` when `T ≥ 1`, and every `β ∈ (0, 1]` has a
candidate with the same sort keys. -/
theorem section_2_derandomize_alg2 (I : Instance) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x) :
    (∀ β ∈ cand I x (numIntervals I ε'), 0 < β ∧ β ≤ 1) ∧
    (cand I x (numIntervals I ε')).card ≤ Fintype.card I.N * numIntervals I ε' + 1 ∧
    (1 ≤ horizon I →
      (numIntervals I ε' : ℝ) ≤ 2 + (1 + ε') * Real.log (horizon I) / ε') ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ β' ∈ cand I x (numIntervals I ε'), key I x β' = key I x β := by sorry

end AndOrSched
