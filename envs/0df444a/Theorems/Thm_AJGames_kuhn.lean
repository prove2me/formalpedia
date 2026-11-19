-- Prove2me | Theorems.Thm_AJGames_kuhn
-- name    : AJGames.kuhn
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:39:44.812317+00:00
-- url     : https://prove2.me/theorems/f7e62e9a-d8ba-4ec2-89e2-18d731cfd985
-- title:
--   Kuhn's theorem for finite AJ games
-- statement:
--   Let $A$ be a game with finitely many moves whose positions have bounded length.
--
--   1. For every behaviour strategy $\beta$ there is a probability distribution $\mu$ on deterministic strategies such that, for every script $r$ and every play $p$,
--   $$\Pr_\beta[\text{play-out against } r \text{ ends at } p]=\sum_\sigma\mu(\sigma)\,\Pr_\sigma[\text{play-out against } r\text{ ends at } p].$$
--   2. Conversely, every such distribution $\mu$ has a behaviour strategy $\beta$ with the same play-out distributions.
--
--   AJ plays record the whole history, so Player has perfect recall.
-- source:
--   H. W. Kuhn, Extensive games and the problem of information, Contributions to the Theory of Games II, Annals of Mathematics Studies 28 (1953) 193-216, Theorem 4 (behaviour and mixed strategies are equivalent under perfect recall), for the finite AJ games of S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057

import Mathlib
import Definitions.Def_AJGames_Behaviour

namespace AJGames

open scoped ENNReal

universe u

/-- **Kuhn's theorem for finite AJ games.** In a game with finitely many moves and plays of bounded
length, every behaviour strategy has a mixed strategy (a probability distribution on deterministic
strategies) with the same play-out distribution against every Opponent script, and every mixed
strategy has an equivalent behaviour strategy. -/
theorem kuhn {A : Game.{u}} [Finite A.M] (hfin : ∃ N : ℕ, ∀ s ∈ A.pos, s.length ≤ N) :
    (∀ β : BehStrategy A, ∃ μ : PMF (Strategy A), ∀ rs p : List A.M,
      playOut β [] rs p = ∑' σ, μ σ * playOut (ofStrategy σ) [] rs p) ∧
    (∀ μ : PMF (Strategy A), ∃ β : BehStrategy A, ∀ rs p : List A.M,
      playOut β [] rs p = ∑' σ, μ σ * playOut (ofStrategy σ) [] rs p) := by sorry

end AJGames
