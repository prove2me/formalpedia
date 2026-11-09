-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_posCNF_pspaceHard
-- name    : ArcKayles192.PSPACE.posCNF_pspaceHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:00:08.787201+00:00
-- url     : https://prove2.me/theorems/85c03572-7bdf-4e66-9a7c-c0266bd2cb03
-- title:
--   Pos CNF is PSPACE-hard (Schaefer 1978, cited as [13])
-- statement:
--   The decision problem POS CNF is PSPACE-hard: given a Pos CNF instance $\varphi$, deciding whether True, moving first, has a winning strategy in the game where True and False alternately claim unclaimed variables (True setting hers to true, False setting his to false) and True wins iff every clause ends up satisfied, is PSPACE-hard under polynomial-time many-one reductions:
--   $$\textsf{POS CNF}\ \text{is}\ \mathsf{PSPACE}\text{-hard}.$$
--
--   This is Schaefer's theorem, cited by the paper and used as the source of its reduction.
--
--   Differences from the source:
--   - encoding: a Pos CNF instance φ = C_1 ∧ ⋯ ∧ C_m over x_1, …, x_n with positive clauses, no encoding fixed → PosCNF: n, m and clause : Fin m → Finset (Fin n) (empty and repeated clauses allowed); enc = 1^n 0 1^m 0 then the m·n incidence bits clause by clause; reason: the paper's definition (p.4) does not exclude empty or repeated clauses; the encoding is the standard incidence-matrix one, injective and of polynomial length
--   - encoding: True wins if she has a winning strategy in the alternating claiming game (p.4) → PosCNF.TrueWins φ T F trueToMove by backward induction on the unclaimed variables, positions being the sets T (claimed by True) and F (claimed by False); reason: finite determined game; "False has a winning strategy" is the negation of TrueWins
--   - encoding: PSPACE, PSPACE-hard, PSPACE-complete in the standard sense → the published OptimalQueuingComplexity.Restless predicates over Mathlib multi-stack machines (FinTM2), space = total stack length, reductions = TM2ComputableInPolyTime; reason: standard machine model; multi-stack machines and Turing machines simulate each other with polynomial overhead
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.4 §2.2 and p.5 (citing [13] = T. J. Schaefer, On the complexity of some two-person perfect-information games, JCSS 16(2):185–225, 1978)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace ArcKayles192.PSPACE

open OptimalQueuingComplexity.Restless

/-- **Pos CNF is PSPACE-hard** (Schaefer 1978, cited as [13] on pp.4–5). Deciding whether True,
moving first, has a winning strategy in the Pos CNF game is PSPACE-hard. -/
theorem posCNF_pspaceHard : PSPACEHard PosCNF.enc posCNF := by sorry

end ArcKayles192.PSPACE
