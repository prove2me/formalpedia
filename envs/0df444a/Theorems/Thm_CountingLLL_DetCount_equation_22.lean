-- Prove2me | Theorems.Thm_CountingLLL_DetCount_equation_22
-- name    : CountingLLL.DetCount.equation_22
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:24:51.677731+00:00
-- url     : https://prove2.me/theorems/edaca105-7051-478d-b6ad-f9440ea09cca
-- title:
--   Distant free constraints are outside radius two (equation 22)
-- statement:
--   For every rooted canonical 2-tree T, the free constraints outside free^1(T) are exactly the constraints at graph distance greater than two from T. Equivalently, free(T)\free^1(T)=E\Gamma^(<=2)(T). This is equation (22), and identifies the base family in the randomized counting recursion.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, equation (22), Section 5.1, PDF p.15, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.equation_22 (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Φ.free E r T \ Φ.free1 E r T =
      E \ E.filter (fun c => distSet (Φ.depGraph E) c T ≤ 2) := by sorry
