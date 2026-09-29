-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
-- name    : AlgebraicCurve.Place.evalAt_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/530bce27-196e-589d-a3d0-19d0844fb39d
-- title:
--   Evaluation of a constant at a place returns the constant
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of this development: a valuation subring $v.\mathrm{toValuationSubring}$ of $F$ which contains $\mathrm{algebraMap}_{K,F}(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring. For $f \in F$ the evaluation $v.\mathrm{evalAt}(f) \in K$ is defined to be $0$ when $f$ does not lie in $v.\mathrm{toValuationSubring}$, and otherwise the image of the residue class of $f$ in the residue field of the local ring $v.\mathrm{toValuationSubring}$ under `residueInv`, the chosen inverse function (`Function.invFun`) of the structure map $K \to v.\mathrm{ResidueField}$. The assertion is that for every $a \in K$ one has $v.\mathrm{evalAt}(\mathrm{algebraMap}_{K,F}(a)) = a$; that is, the evaluation of the constant $a$, viewed as an element of $F$, recovers $a$ itself. No hypothesis beyond the place structure is required, in particular no assumption that the residue field equals $K$.
--
--   This is the statement that constants are evaluated to themselves at any place of $F/K$, the base case of the evaluation-of-functions layer used in the treatment of divisors, Weil reciprocity and the Weil pairing; it is invoked throughout that layer, for instance in the computations on annuli and component charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_algebraMap.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by sorry
