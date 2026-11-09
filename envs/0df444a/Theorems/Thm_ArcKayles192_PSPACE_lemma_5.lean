-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_lemma_5
-- name    : ArcKayles192.PSPACE.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:49.296764+00:00
-- url     : https://prove2.me/theorems/08988488-d25c-4c4c-9a7d-6e200a842ee3
-- title:
--   Lemma 5: the Pos CNF game is outcome-equivalent to its variant with passes and free truth values
-- statement:
--   Let $\varphi$ be a Pos CNF instance and let $(T,F)$ be a position: disjoint sets of variables set to true and to false, with either player to move. For every pass budget $p\in\mathbb N$,
--   $$\mathrm{TrueWins}(\varphi,T,F,\text{mover})\iff\mathrm{TrueWinsVar}(\varphi,T,F,\text{mover},p).$$
--   That is, True wins the Pos CNF game from this position iff True wins the variant in which, in addition, the player to move may pass (at most $p$ passes in total, shared by both players) or may give the selected variable either truth value.
--
--   Since both games are finite and determined, this says that the first player (the one to move) and the second player have winning strategies from the same positions in both games, which is the paper's outcome-equivalence. The proof of Claims 9 and 10 uses it to let the simulating player ignore the opponent's passes and helpful assignments.
--
--   Differences from the source:
--   - reading: the variant where players can additionally pass, with no rule for an infinite run of passes → a shared pass budget p, every p ∈ ℕ; a pass costs one unit, the play ends when all variables are claimed; reason: the paper does not say who wins an infinite play of passes; in G_φ passes are the finitely many pass edges, shared by both players, so a finite shared budget is how the lemma is used; stating it for every p never fixes the budget
--   - encoding: outcome-equivalent: the first player (resp. second player) wins from the same positions → for every position and either mover, TrueWins ↔ TrueWinsVar; reason: both games are finite and determined, so the mover wins iff (True moves and True wins) or (False moves and True does not win), and the second clause is the negation of the first
--   - encoding: True wins if she has a winning strategy in the alternating claiming game (p.4) → PosCNF.TrueWins φ T F trueToMove by backward induction on the unclaimed variables, positions being the sets T (claimed by True) and F (claimed by False); reason: finite determined game; "False has a winning strategy" is the negation of TrueWins
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.4, Lemma 5 (and the definition of outcome-equivalent just above it)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_PosCNF

namespace ArcKayles192.PSPACE

/-- **Lemma 5** (p.4). The Pos CNF game is outcome-equivalent to its variant where players can
additionally pass (here from a shared budget of `p` passes, for every `p`) or assign either truth
value to the selected variable: from every position (disjoint sets `T`, `F` of variables set to
true and false, either player to move) True wins the Pos CNF game iff True wins the variant. -/
theorem lemma_5 (φ : PosCNF) (T F : Finset (Fin φ.n)) (hTF : Disjoint T F)
    (trueToMove : Bool) (p : ℕ) :
    PosCNF.TrueWins φ T F trueToMove ↔ PosCNF.TrueWinsVar φ T F trueToMove p := by sorry

end ArcKayles192.PSPACE
