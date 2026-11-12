-- Prove2me | Theorems.Thm_BunkbedTM_class_products
-- name    : BunkbedTM.class_products
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T16:04:54.188042+00:00
-- url     : https://prove2.me/theorems/7079abff-2b8f-4edf-ad33-972e9fb6d69e
-- title:
--   The fifteen class products are the Wierman--Ziff difference polynomial
-- statement:
--   This is the algebraic heart of Lemma 3.3: the fifteen class products of `BunkbedTransferClasses` sum to the explicit degree-$12$ difference polynomial `wzDiffPoly`.
--
--   Both sides are homogeneous of degree $12$ in $x = P_{abc}$, $y = P_{a|b|c}$, $z = P_{a|bc}$, $u = P_{ab|c} = P_{ac|b}$, with $231$ monomials when fully expanded. The right-hand side is written in the graded form that makes Lemma 3.3's estimate transparent: with $W = xy - u^2$ the determinant-like quantity of Eq. [1], the coefficient of $z^j$ is divisible by $W^{6-j}$ for $j \le 6$, and the $z$-free term is exactly $W^6$ — those being the configurations in which every hyperedge is fully present on one level and absent on the other, which is precisely the alternative model.
--
--   Checking the identity one power of $z$ at a time turns a single four-variable polynomial identity into thirteen three-variable ones, whose right-hand sides are the graded cofactors $W^{6-n} R_n$.
-- source:
--   Gladkov, Pak, Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) no. 24, e2420725122; Section 3, Lemma 3.3 and Hollom's 3-uniform hypergraph (Fig. 1), with the path $\rho$ of Eq. [5].

import Definitions.Def_BunkbedTransferClasses
import Definitions.Def_BunkbedWZPoly
open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

theorem BunkbedTM.class_products (x y z u : Rat) :
    ck0 x y z u * wk0 x y z u + ck1 x y z u * wk1 x y z u + ck2 x y z u * wk2 x y z u + ck3 x y z u * wk3 x y z u + ck4 x y z u * wk4 x y z u + ck5 x y z u * wk5 x y z u + ck6 x y z u * wk6 x y z u + ck7 x y z u * wk7 x y z u + ck8 x y z u * wk8 x y z u + ck9 x y z u * wk9 x y z u + ck10 x y z u * wk10 x y z u + ck11 x y z u * wk11 x y z u + ck12 x y z u * wk12 x y z u + ck13 x y z u * wk13 x y z u + ck14 x y z u * wk14 x y z u
      = wzDiffPoly x y z u := by sorry
