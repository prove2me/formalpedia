-- Prove2me | Theorems.Thm_AJGames_ofStrategy_playProb
-- name    : AJGames.ofStrategy_playProb
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:32:47.431205+00:00
-- url     : https://prove2.me/theorems/71b631de-686e-4b1d-a394-b3a861d52b40
-- title:
--   Deterministic strategies embed conservatively into behaviour strategies
-- statement:
--   Let $\sigma$ be a strategy on a game $A$, read as a behaviour strategy. For every position $s$ of $A$, the probability of $s$ under it is
--   $$\Pr(s)=\begin{cases}1 & s\in\sigma,\\ 0 & s\notin\sigma.\end{cases}$$
--
--   So behaviour strategies extend deterministic ones without changing them.
-- source:
--   New statement introduced by this mission (no prior source); the notion of behaviour strategy is from H. W. Kuhn, Extensive games and the problem of information, Contributions to the Theory of Games II, Annals of Mathematics Studies 28 (1953) 193-216

import Mathlib
import Definitions.Def_AJGames_Behaviour

namespace AJGames

open scoped ENNReal

universe u

open Classical in
/-- **Behaviour strategies extend deterministic ones conservatively.** Read as a behaviour strategy,
a deterministic strategy `σ` gives every position probability `1` if it lies in `σ` and `0`
otherwise. AJ axioms used: G2 (prefix closure) and G3 (alternation, to see that Player is to move
before a Player move); the strategy axioms first-O, determinism and receptiveness. No tensor axiom. -/
theorem ofStrategy_playProb {A : Game.{u}} (σ : Strategy A) (s : List A.M) (hs : s ∈ A.pos) :
    playProb (ofStrategy σ) s = if s ∈ σ.carrier then 1 else 0 := by sorry

end AJGames
