-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_revelation_principle
-- name    : AlgMechDesign.LowerBound.revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:41:46.59464+00:00
-- url     : https://prove2.me/theorems/dce4c1fe-dda8-408f-8670-dfcf53073bd7
-- title:
--   Proposition 2.1 — revelation principle for task scheduling
-- statement:
--   Consider the task scheduling problem with $n \ge 1$ agents and $k$ tasks, and let $m=(o,p)$ be a general mechanism with arbitrary strategy sets $A^1,\dots,A^n$. Suppose $m$ implements a $c$-approximation with dominant strategies: every agent of every positive type $t^i$ has a dominant strategy, and whenever each agent plays a dominant strategy for its type, the resulting allocation has make-span at most $c$ times the make-span of any allocation.
--
--   Then there is a direct mechanism $(x, p^*)$ — agents simply report types — that is truthful and whose allocation rule is a $c$-approximation:
--
--   $$
--   \text{truth-telling is dominant in } (x,p^*) \quad\text{and}\quad g(x(t),t) \le c\cdot g(y,t) \ \text{ for all positive } t \text{ and all allocations } y .
--   $$
--
--   This is the revelation principle; it lets the lower bound of Theorem 4.6 be proved for truthful direct mechanisms only.
--
--   **Formalization Note** The paper states the proposition for an arbitrary mechanism design problem; it is formalized here for task scheduling with the $c$-approximation specification, which is the only use made of it. "Truthful implementation" is read as: truth-telling is dominant (Definition 4) and the output at truthful reports satisfies the specification. The literal second bullet of Definition 3 ("for each tuple of dominant strategies") is not required of the direct mechanism, because a report that is dominant in the simulating mechanism need not correspond to a dominant strategy of the original.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 172, Proposition 2.1 (proof sketch p. 173)

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model
import Definitions.Def_AlgMechDesign_LowerBound_Mechanism

namespace AlgMechDesign.LowerBound

universe u

/-- Proposition 2.1 (revelation principle), specialised to task scheduling: if a general
mechanism `(o, p)` with strategy sets `A i` implements a `c`-approximation with dominant
strategies, then some direct mechanism `(alloc, pay)` on type vectors is truthful and its
allocation rule is a `c`-approximation. -/
theorem revelation_principle {n k : ℕ} [NeZero n] {A : Fin n → Type u}
    (o : ((i : Fin n) → A i) → (Fin k → Fin n)) (p : ((i : Fin n) → A i) → Fin n → ℝ) {c : ℝ}
    (h : Implements o p c) :
    ∃ (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ),
      IsTruthful alloc pay ∧ IsApprox c alloc := by sorry

end AlgMechDesign.LowerBound
