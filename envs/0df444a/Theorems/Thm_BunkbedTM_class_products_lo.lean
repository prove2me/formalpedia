-- Prove2me | Theorems.Thm_BunkbedTM_class_products_lo
-- name    : BunkbedTM.class_products_lo
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T16:52:42.30524+00:00
-- url     : https://prove2.me/theorems/1dcb101c-79d5-4d6b-a3cb-078119476015
-- title:
--   The first eight class products of Hollom's hypergraph
-- statement:
--   The Wierman--Ziff difference polynomial of Hollom's hypergraph is the sum of fifteen products $(\mathtt{ck}\,k)(\mathtt{wk}\,k)$, one for each of the fifteen classes into which the $47$ level-$1$ profiles fall. This statement verifies the first eight of them against the expanded polynomial `wzDlo`.
--
--   Both sides are homogeneous of degree $12$ in $x = P_{abc}$, $y = P_{a|b|c}$, $z = P_{a|bc}$, $u = P_{ab|c} = P_{ac|b}$. Splitting the fifteen products into two halves keeps each half inside the compile budget; grading both sides by powers of $z$ then replaces one four-variable polynomial identity by thirteen three-variable ones, which is what makes the `ring` normalisation affordable.
-- source:
--   Gladkov, Pak, Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) no. 24, e2420725122; Section 3, Lemma 3.3.

import Definitions.Def_BunkbedTransferPartial
open Bunkbed Bunkbed.Hyper Bunkbed.TM

theorem BunkbedTM.class_products_lo (x y z u : Rat) :
    ck0 x y z u * wk0 x y z u + ck1 x y z u * wk1 x y z u + ck2 x y z u * wk2 x y z u + ck3 x y z u * wk3 x y z u + ck4 x y z u * wk4 x y z u + ck5 x y z u * wk5 x y z u + ck6 x y z u * wk6 x y z u + ck7 x y z u * wk7 x y z u
      = wzDlo x y z u := by sorry
