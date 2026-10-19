-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_scaling_step
-- name    : CloudMWU.Bicriteria.scaling_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:40.609924+00:00
-- url     : https://prove2.me/theorems/fe5431e7-8602-4e3d-b8ea-bdcd468cb214
-- title:
--   p. 10, reduction of Theorem 1 to Theorems 3–4 — scaling an allocation by κ ≤ 1 keeps ≥ κ of its work; cumulative work is monotone in the allocation
-- statement:
--   Consider a single user with a nonnegative load sequence $\ell$ and queues starting empty, and write $W_t(a)$ for the work that the allocation sequence $a$ completes in the first $t$ steps.
--
--   1. **Scaling.** For every $0 \le \kappa \le 1$, every allocation sequence $a$ and every $t$,
--   $$\kappa\, W_t(a) \;\le\; W_t(\kappa a).$$
--   2. **Monotonicity.** If $a_\tau \le b_\tau$ for every $\tau$, then $W_t(a) \le W_t(b)$ for every $t$.
--
--   This is the step of p. 10 that turns Theorems 3 and 4 into Theorem 1: the work pattern $\kappa w_1, \kappa w_2, \dots$ of an allocation $a$ is feasible for the scaled allocation $\kappa a$ with the same loads, and users always use their allocations at maximum. It is used with $\kappa = 1 - 4\varepsilon$ (work maximization) and $\kappa = 1 - 2\varepsilon$ (SLA satisfaction), and monotonicity is used to compare an arbitrary comparator $h'_t(i) \le \beta(i)$ with the constant allocation $\beta(i)$.
--
--   **Formalization Note** The paper's sentence concludes "$(1-\varepsilon)\,\mathrm{work}_h \le \mathrm{work}_{\bar h}$" where its own display has $(1 - 4\varepsilon)$ and $\bar h = (1-4\varepsilon)h$; the statement is given for a general factor $\kappa \in [0,1]$, which covers both. Stated per user, since users' queues do not interact. No sign condition on the allocations is needed.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 10, reduction of Theorem 1 part 1 to Theorem 3 ('To argue the second, …')

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Queue

namespace CloudMWU.Bicriteria

open Finset

theorem scaling_step (ℓ : ℕ → ℝ) (hℓ : ∀ t, 0 ≤ ℓ t) :
    (∀ (κ : ℝ), 0 ≤ κ → κ ≤ 1 → ∀ (a : ℕ → ℝ) (t : ℕ),
      κ * cumWork a ℓ t ≤ cumWork (fun τ => κ * a τ) ℓ t) ∧
    (∀ (a b : ℕ → ℝ), (∀ τ, a τ ≤ b τ) → ∀ t : ℕ, cumWork a ℓ t ≤ cumWork b ℓ t) := by sorry

end CloudMWU.Bicriteria
