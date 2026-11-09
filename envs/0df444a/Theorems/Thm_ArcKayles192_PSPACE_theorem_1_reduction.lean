-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_theorem_1_reduction
-- name    : ArcKayles192.PSPACE.theorem_1_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:34.517203+00:00
-- url     : https://prove2.me/theorems/944c89d9-a12f-4fee-9aa6-baef69f8a444
-- title:
--   Theorem 1, the reduction: Pos CNF polynomial-time many-one reduces to Arc Kayles
-- statement:
--   There is a polynomial-time many-one reduction from POS CNF to ARC KAYLES: a map $\varphi\mapsto G$, computed by a Turing machine in polynomial time on the encodings, such that True wins the Pos CNF game on $\varphi$ iff the first player wins Arc Kayles on $G$:
--   $$\textsf{POS CNF}\le_p\textsf{ARC KAYLES}.$$
--
--   The paper's map duplicates a clause when $m$ is even and then builds $G_\varphi$, which has $2+2m+2K+2R+n=O(n+m)$ vertices. The statement asserts only that some such reduction exists.
--
--   Differences from the source:
--   - encoding: a Pos CNF instance φ = C_1 ∧ ⋯ ∧ C_m over x_1, …, x_n with positive clauses, no encoding fixed → PosCNF: n, m and clause : Fin m → Finset (Fin n) (empty and repeated clauses allowed); enc = 1^n 0 1^m 0 then the m·n incidence bits clause by clause; reason: the paper's definition (p.4) does not exclude empty or repeated clauses; the encoding is the standard incidence-matrix one, injective and of polynomial length
--   - encoding: True wins if she has a winning strategy in the alternating claiming game (p.4) → PosCNF.TrueWins φ T F trueToMove by backward induction on the unclaimed variables, positions being the sets T (claimed by True) and F (claimed by False); reason: finite determined game; "False has a winning strategy" is the negation of TrueWins
--   - encoding: Arc Kayles instances are finite graphs, with no encoding fixed → GraphInstance: n and a symmetric irreflexive Boolean n × n matrix; enc = 1^n 0 followed by the n² adjacency bits row by row; reason: the standard adjacency-matrix encoding, injective, of length n² + n + 1
--   - encoding: PSPACE, PSPACE-hard, PSPACE-complete in the standard sense → the published OptimalQueuingComplexity.Restless predicates over Mathlib multi-stack machines (FinTM2), space = total stack length, reductions = TM2ComputableInPolyTime; reason: standard machine model; multi-stack machines and Turing machines simulate each other with polynomial overhead
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, pp.5–6, proof of Theorem 1 (reduction from Pos CNF; construction and its size, p.6)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace ArcKayles192.PSPACE

open OptimalQueuingComplexity.Restless

/-- **Theorem 1, the reduction** (proof of Theorem 1, pp.5–6). POS CNF polynomial-time many-one
reduces to ARC KAYLES, for the encodings `PosCNF.enc` and `GraphInstance.enc`. -/
theorem theorem_1_reduction : PolyReduces PosCNF.enc posCNF GraphInstance.enc arcKayles := by sorry

end ArcKayles192.PSPACE
