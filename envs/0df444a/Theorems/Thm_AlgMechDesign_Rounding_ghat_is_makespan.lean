-- Prove2me | Theorems.Thm_AlgMechDesign_Rounding_ghat_is_makespan
-- name    : AlgMechDesign.Rounding.ghat_is_makespan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:11:50.321526+00:00
-- url     : https://prove2.me/theorems/e4bdbb95-3236-4897-9e9c-112101b3eea1
-- title:
--   Proof of Theorem 5.9 — after rounding, $\hat g$ is the make-span and utility equals the rounded bonus
-- statement:
--   Fix a rounding step $\delta$ and any allocation rule $x(\cdot)$.
--
--   1. For every allocation $x$ and declaration profile $d$, the rounded make-span of the time vector $\mathrm{corr}^*(x,d)$ is the make-span of the rounded declarations on $x$:
--   $$\hat g\big(x, \mathrm{corr}^*(x,d)\big) = g(x, \hat d).$$
--   2. In the rounding mechanism, for all declarations $d$, all execution plans and every agent $i$, the utility of agent $i$ equals its bonus:
--   $$u^i = -\hat g\big(x(d), \mathrm{corr}^i(x(d), d, \tilde t)\big),$$
--   where $\tilde t$ are the actual times of the outcome.
--
--   Together these say that, once types and actual times are rounded, the bonus is the negated make-span of a scheduling instance whose optimum the rounding algorithm computes; this is the reduction to the argument of Theorem 5.1.
--
--   **Formalization Note** The second part holds because the compensation exactly cancels the valuation; it needs no hypothesis on the allocation rule.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 193, proof (sketch) of Theorem 5.9, first sentence

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

namespace AlgMechDesign.Rounding

/-- Proof of Theorem 5.9, first sentence (p. 193): after rounding, `ĝ` is exactly the make-span.
(i) For every allocation `x` and declarations `d`, `ĝ(x, corr*(x, d))` is the make-span of the
rounded declarations `d̂` on `x`; (ii) in the rounding mechanism the utility of every agent `i`
equals its rounded bonus `-ĝ(x, corrⁱ(x, d, t̃))`, whatever the declarations and executions. -/
theorem ghat_is_makespan {n k : ℕ} [NeZero n] (δ : ℝ)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    (∀ (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ),
      gT x (roundVec δ (corrStar x d)) = makespan (roundType δ d) x) ∧
    (∀ (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n),
      utility alloc (roundingPay δ alloc) d E i =
        -gT (alloc d) (roundVec δ (corr i (alloc d) d (actualTimes alloc d E)))) := by sorry

end AlgMechDesign.Rounding
