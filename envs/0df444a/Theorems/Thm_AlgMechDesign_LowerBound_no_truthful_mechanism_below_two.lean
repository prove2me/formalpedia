-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_no_truthful_mechanism_below_two
-- name    : AlgMechDesign.LowerBound.no_truthful_mechanism_below_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T18:58:25.355242+00:00
-- url     : https://prove2.me/theorems/6a55b303-6a88-4e32-8745-85d60c17aa58
-- title:
--   Theorem 4.6 for truthful mechanisms — no truthful $c$-approximation for $c<2$
-- statement:
--   Let $n \ge 2$ agents and $k \ge 3$ tasks be given, and let $c < 2$. No truthful direct mechanism $(x,p)$ for task scheduling has an allocation rule that is a $c$-approximation: for every truthful $(x,p)$ there are a positive type vector $t$ and an allocation $y$ with
--
--   $$
--   g\big(x(t),t\big) > c\cdot g(y,t).
--   $$
--
--   By the revelation principle (Proposition 2.1) this is equivalent to Theorem 4.6, and it is the form in which Section 4.3 proves it.
--
--   **Formalization Note** The thresholds $n\ge2$ and $k\ge3$ come from the proof ("We prove the theorem for the case of two agents"; "Let $k\ge3$"); for $n=1$ the claim is false. The statement is for each fixed $n$ and $k$, for every $c<2$, and for every truthful mechanism, with no restriction on tie-breaking.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, opening paragraph of Section 4.3, and p. 178, Theorem 4.6

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

/-- Theorem 4.6 for truthful direct mechanisms (§4.3, p. 177): with at least two agents and at
least three tasks, no truthful direct mechanism for task scheduling has an allocation rule that
is a `c`-approximation for any `c < 2`. -/
theorem no_truthful_mechanism_below_two {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k)
    {c : ℝ} (hc : c < 2) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay) :
    ¬ IsApprox c alloc := by sorry

end AlgMechDesign.LowerBound
