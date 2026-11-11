-- Prove2me | Theorems.Thm_FixedPolyominoSquare_SquareCounting_main_theorem
-- name    : FixedPolyominoSquare.SquareCounting.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:37.022791+00:00
-- url     : https://prove2.me/theorems/b0fdb29d-6530-4246-9576-98e85f4499ec
-- title:
--   Theorem 1.1 — fixed-family square-counting completeness and #E membership
-- statement:
--   There exists one fixed finite family $T^\star$ of pairwise distinct nonempty 4-connected polyominoes in $\mathbb Z^2$ such that its total binary square-counting function satisfies
--
--   $$G_{T^\star}\text{ is }\#\mathrm{EXP}\text{-complete under polynomial-time metric reductions},\qquad G_{T^\star}\in\#E.$$
--
--   The family is chosen before every input. The function counts every geometric translation-only tiling of the ordinary square, without conditioning on a simulated computation. It is one on the canonical code of zero and zero on malformed binary strings. Completeness includes membership in the standard machine-counting class and a reduction from every member of that class. This is the entire headline, including its stronger membership conclusion; it assumes no universal counter, compiler correctness, geometric bijection or resource-bound certificate.
--
--   Differences from the source:
--   - encoding: finite indexed polyomino families and standard finite labelled machines on binary strings → Fin-indexed supports, finite transition tables, accepting halting-leaf counts and explicit binary-pair postprocessor inputs; reason: these are operational encodings of the same families, branches and total bit-time metric reductions; every machine and resource bound precedes all input quantifiers
--   - encoding: a finite set T⋆ = {τ1, …, τk} of polyominoes → a Fin-indexed family with an injective shape map; reason: an injective indexing of a finite set is the same family, and placements (t, v) are indexed exactly as on p. 3
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 2, Theorem 1.1; pp. 23–24, Section 9

import Definitions.Def_FixedPolyominoSquare_SquareCounting_PolyominoModel
import Definitions.Def_FixedPolyominoSquare_SquareCounting_FiniteMachine

namespace FixedPolyominoSquare.SquareCounting

/-- Chen--Xie, Theorem 1.1, p. 2. One fixed finite family, all geometric tilings,
canonical binary inputs, both standard counting-class conclusions. The prototiles
are pairwise distinct (`T.shape` injective), since the source's family is a set. -/
theorem main_theorem :
    ∃ T : TileFamily, Function.Injective T.shape ∧ (∀ t, IsPolyomino (T.shape t)) ∧
      SharpEXPComplete (G T) ∧ SharpE (G T) := by sorry

end FixedPolyominoSquare.SquareCounting
