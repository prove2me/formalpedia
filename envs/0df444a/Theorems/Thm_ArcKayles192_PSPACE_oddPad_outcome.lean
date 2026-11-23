-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_oddPad_outcome
-- name    : ArcKayles192.PSPACE.oddPad_outcome
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:21.165809+00:00
-- url     : https://prove2.me/theorems/9e70dadd-6f76-4fc7-bee1-04bddc96a8e4
-- title:
--   Duplicating a clause to make the clause count odd preserves the Pos CNF outcome
-- statement:
--   For a Pos CNF instance $\varphi$, let $\operatorname{oddPad}(\varphi)$ leave $\varphi$ unchanged when its number $m$ of clauses is odd or zero, and otherwise append a second copy of $C_1$. Then
--   $$
--   \operatorname{TrueWins}(\operatorname{oddPad}(\varphi))
--   \quad\Longleftrightarrow\quad
--   \operatorname{TrueWins}(\varphi).
--   $$
--
--   This is the padding step at the start of the reduction in Theorem 1: it ensures that Claims 7–10 can be applied with an odd clause count without changing the winner. The case $m=0$ is included and the padding is then literally the identity.
--
--   **Formalization Note.** Both games use the published `PosCNF.TrueWins` recursion from the empty position, with True moving first; repeated clauses and empty clauses are allowed.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.5, proof of Theorem 1: 'We simply duplicate one clause if this is not the case, as this does not change which player has a winning strategy.' The m=0 identity case makes the instruction total.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_ArcKayles192_PSPACE_ReductionInstance

/-- **Padding invariance** (proof of Theorem 1, p.5). `oddPad` duplicates the first clause exactly
when the positive number of clauses is even, and otherwise leaves the formula unchanged. True has a
winning strategy in the Pos CNF game on the padded formula iff she has one on the original formula. -/
theorem ArcKayles192.PSPACE.oddPad_outcome (φ : ArcKayles192.PSPACE.PosCNF) :
    ArcKayles192.PSPACE.posCNF (ArcKayles192.PSPACE.oddPad φ) ↔
      ArcKayles192.PSPACE.posCNF φ := by sorry
