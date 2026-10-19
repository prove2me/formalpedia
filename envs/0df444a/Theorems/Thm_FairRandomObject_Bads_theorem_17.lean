-- Prove2me | Theorems.Thm_FairRandomObject_Bads_theorem_17
-- name    : FairRandomObject.Bads.theorem_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:42.654592+00:00
-- url     : https://prove2.me/theorems/643313e5-a34d-4292-857c-c9a7bda07917
-- title:
--   Theorem 17, p. 16 — for n ≥ 2 the Bottom-Heavy rule ϕ¹ is a fair symmetric API rule for bads and dominates every other one
-- statement:
--   Let $n\ge2$ agents share a random bad. The Bottom-Heavy rule $\varphi^1$ (Definition 15) dominates every other symmetric almost prior-independent rule for bads satisfying Fair Share. Precisely:
--
--   1. $\varphi^1$ is a symmetric API rule and satisfies Fair Share: $\mathbb E_\mu(\varphi^1_i(X)X_i)\le1/n$ for every normalized problem $\mu$ and every agent $i$;
--   2. for every symmetric API rule $\varphi$ satisfying Fair Share with $\varphi(x)\ne\varphi^1(x)$ for some $x\in\mathbb R^N_+$,
--   $$\sum_{i\in N}\varphi^1_i(x)\,x_i\le\sum_{i\in N}\varphi_i(x)\,x_i\quad\text{for all }x\in\mathbb R^N_+,$$
--   with strict inequality for some $x\in\mathbb R^N_+$.
--
--   So among fair prior-independent rules for a bad there is a single most efficient one, ex post at every realization.
--
--   **Formalization Note** $\varphi^1$ is the $\theta=1$ member of the family (13); for $x_i>0$ its prefix shares are $x_{N\setminus\{i\}}/(n(n-1)x_i)$, and when some agents have zero disutility they split the bad equally (the paper's $\bar x/0=+\infty$). Fair Share ranges over all normalized laws on $\mathbb R^N_+$, not only finitely supported ones. Part 1 is the presupposition of "every **other**" and is stated explicitly.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 16, Theorem 17

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 16, Theorem 17 (for bads): for any `n ≥ 2`, the Bottom-Heavy rule
`ϕ¹` dominates every other symmetric API rule for bads satisfying Fair Share.

The statement has two parts: `ϕ¹` is itself a symmetric API rule satisfying Fair Share (the
"other" presupposes it), and every symmetric API rule `ϕ` satisfying Fair Share that differs
from `ϕ¹` at some profile of `ℝ^N_+` is dominated by `ϕ¹`: weakly lower social cost
`∑_i ϕ_i(x) x_i` at every `x ∈ ℝ^N_+`, strictly lower at some `x ∈ ℝ^N_+`.

**Formalization Note.** `ϕ¹ = bottomHeavy n 1`, which for `x_i > 0` assigns the shares
`x_{N∖{i}}/(n(n−1)x_i)` of Definition 15, (10) (see `psi_one_eq`), and splits the bad equally
among zero-disutility agents when there are any (the paper's `x̄/0 = +∞`). Agents are `Fin n`;
Fair Share ranges over all normalized laws on `ℝ^N_+`. -/
theorem theorem_17 {n : ℕ} (hn : 2 ≤ n) :
    (IsAPIRule (bottomHeavy n 1) ∧ IsSymmetric (bottomHeavy n 1) ∧
        FairShareBad (bottomHeavy n 1)) ∧
      ∀ ϕ : Rule n, IsAPIRule ϕ → IsSymmetric ϕ → FairShareBad ϕ →
        (∃ x : Fin n → ℝ, 0 ≤ x ∧ ϕ x ≠ bottomHeavy n 1 x) →
        DominatesBad (bottomHeavy n 1) ϕ := by sorry

end FairRandomObject.Bads
