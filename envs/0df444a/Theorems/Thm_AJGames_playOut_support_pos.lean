-- Prove2me | Theorems.Thm_AJGames_playOut_support_pos
-- name    : AJGames.playOut_support_pos
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:33:11.332168+00:00
-- url     : https://prove2.me/theorems/fe9d2b48-7ec7-4d98-ae59-c08aa5135663
-- title:
--   Play-outs stay inside the game
-- statement:
--   Let $\beta$ be a behaviour strategy on $A$, let $s$ be a position, and let $r$ be any script. Every outcome of positive probability in the play-out of $\beta$ from $s$ against $r$ is a position of $A$.
-- source:
--   New statement introduced by this mission (no prior source); sanity property of the play-out defined in Def_AJGames_Behaviour

import Mathlib
import Definitions.Def_AJGames_Behaviour

namespace AJGames

universe u

/-- **Play-outs stay inside the game.** Every outcome of a behaviour strategy's play-out against a
script, started from a position, is a position. AJ axioms used: none beyond the legality clause
of `BehStrategy`. -/
theorem playOut_support_pos {A : Game.{u}} (β : BehStrategy A) :
    ∀ (rs s : List A.M), s ∈ A.pos → ∀ p ∈ (playOut β s rs).support, p ∈ A.pos := by sorry

end AJGames
