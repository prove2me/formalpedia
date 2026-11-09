-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_claim_10
-- name    : ArcKayles192.PSPACE.claim_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:03.307262+00:00
-- url     : https://prove2.me/theorems/787fff9c-a65d-40b5-bdf9-14ec25ef53f2
-- title:
--   Claim 10: if True wins Pos CNF on $\varphi$, the first player wins Arc Kayles on $G_\varphi$
-- statement:
--   Let $\varphi$ be a Pos CNF instance with an odd number $m$ of clauses. If True has a winning strategy on $\varphi$, then Arc Kayles on $G_\varphi$ is won by the first player:
--   $$\textsf{POS CNF}(\varphi)\ \Longrightarrow\ V(G_\varphi)\ \text{is an N-position}.$$
--   No other hypothesis is assumed: $n=0$ and empty or repeated clauses are allowed.
--
--   Differences from the source:
--   - encoding: P-position / N-position defined through winning strategies (p.2) → FirstPlayerWins G S defined by backward induction on |S|; a P-position is its negation; reason: the game tree is finite, so the player to move has a winning strategy iff some move leads to a position not won by the next player to move; determinacy is built in
--   - encoding: True wins if she has a winning strategy in the alternating claiming game (p.4) → PosCNF.TrueWins φ T F trueToMove by backward induction on the unclaimed variables, positions being the sets T (claimed by True) and F (claimed by False); reason: finite determined game; "False has a winning strategy" is the negation of TrueWins
--   - encoding: 1-based indices a_j, b_j (j ∈ [m]), v_i, t_i (i ∈ [R]), f_i (i ∈ [n]), y_i, z_i (i ∈ [K]) → 0-based indices in Fin m, Fin R, Fin n, Fin K; v_i for i ∈ [n] is v ⟨i, _⟩ with i < n; the paper's pass edges v_i t_i, i ∈ [n+1, R], are those with n ≤ i < R; reason: re-indexing only; no instance changes
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.8, Claim 10 (proof pp.8–9)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_Construction

namespace ArcKayles192.PSPACE

/-- **Claim 10** (p.8). Let `m` be odd. If True has a winning strategy on `φ`, then Arc Kayles on
`G_φ` is won by the first player. -/
theorem claim_10 (φ : PosCNF) (hm : Odd φ.m) (hT : posCNF φ) :
    FirstPlayerWins (Gphi φ) Finset.univ := by sorry

end ArcKayles192.PSPACE
