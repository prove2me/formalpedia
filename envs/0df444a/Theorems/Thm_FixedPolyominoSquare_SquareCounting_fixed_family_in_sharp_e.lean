-- Prove2me | Theorems.Thm_FixedPolyominoSquare_SquareCounting_fixed_family_in_sharp_e
-- name    : FixedPolyominoSquare.SquareCounting.fixed_family_in_sharp_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:42.204188+00:00
-- url     : https://prove2.me/theorems/4f0b21ce-60fc-41c9-b556-b5ab7749f04b
-- title:
--   Proposition 2.1 — fixed-family square counts lie in #E
-- statement:
--   Let $T$ be any fixed finite indexed family of nonempty connected polyominoes in $\mathbb Z^2$, allowing the empty family. The total function $G_T$ counts all translation-only tilings on canonical binary square inputs and is zero on other strings. Then
--
--   $$G_T\in\#E.$$
--
--   The uniform machine and constants may depend on the fixed family, but not on the input. The code of zero has count one. This supplies the membership conclusion independently of every hardness construction.
--
--   **Formalization Note** The class uses one finite machine and fixed natural $c,d$ with time $2^{c|x|+d}$. The source gives a polynomial verification algorithm on witnesses of length $O(n^2|\operatorname{bin}(n)|)$, rather than a specific numerical exponent; the existential linear-exponential class bound preserves exactly that uniform meaning.
--
--   Differences from the source:
--   - encoding: finite indexed polyomino families and standard finite labelled machines on binary strings → Fin-indexed supports, finite transition tables, accepting halting-leaf counts and explicit binary-pair postprocessor inputs; reason: these are operational encodings of the same families, branches and total bit-time metric reductions; every machine and resource bound precedes all input quantifiers
--   - generalization: a finite family T = {τ1, …, τk} of polyominoes (a set, so distinct prototiles) → a Fin-indexed family whose shape map need not be injective; reason: a family with pairwise distinct shapes is a special case, so the Lean statement specializes to the source's claim
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 3, Proposition 2.1

import Definitions.Def_FixedPolyominoSquare_SquareCounting_PolyominoModel
import Definitions.Def_FixedPolyominoSquare_SquareCounting_FiniteMachine

namespace FixedPolyominoSquare.SquareCounting

/-- Chen--Xie, Proposition 2.1, p. 3. The empty family is allowed. -/
theorem fixed_family_in_sharp_e (T : TileFamily) (hT : ∀ t, IsPolyomino (T.shape t)) :
    SharpE (G T) := by sorry

end FixedPolyominoSquare.SquareCounting
