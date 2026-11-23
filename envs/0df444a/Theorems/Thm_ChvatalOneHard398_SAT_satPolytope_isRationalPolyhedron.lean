-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_satPolytope_isRationalPolyhedron
-- name    : ChvatalOneHard398.SAT.satPolytope_isRationalPolyhedron
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:15:18.762452+00:00
-- url     : https://prove2.me/theorems/ddd6297f-851e-4d2c-98fe-826093fceacb
-- title:
--   SAT polytopes are rational polyhedra
-- statement:
--   For every formula $F$ on $N$ Boolean variables, its SAT polytope
--
--   $$
--   P(F)=\left\{x\in[0,1]^N:\sum_{\ell\in T}\ell(x)\ge 1\ \text{for every clause }T\in F\right\}
--   $$
--
--   is a rational polyhedron. Indeed, the bounds $0\le x_i\le1$ and every clause inequality can be written as a finite linear system whose coefficients and right-hand sides are integers (and hence rational). This statement also covers the formalization's totalized literal values on malformed formulas: an out-of-range literal is the constant zero, so its clause still gives a rational linear inequality.
--
--   This elementary presentation fact allows hereditary rank-one results for rational subpolyhedra to be specialized to $P(F)$ itself.
-- source:
--   Alberto Del Pia, STOC 2027 submission #398, p.17, definition of the SAT polytope as a finite system with integer coefficients; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

open CombOpt.ChvatalRank

theorem ChvatalOneHard398.SAT.satPolytope_isRationalPolyhedron
    (F : ChvatalOneHard398.SAT.Formula) :
    IsRationalPolyhedron (ChvatalOneHard398.SAT.satPolytope F) := by sorry
