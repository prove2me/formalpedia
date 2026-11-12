-- Prove2me | Theorems.Thm_BunkbedTM_delta_contract
-- name    : BunkbedTM.delta_contract
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T16:01:58.709964+00:00
-- url     : https://prove2.me/theorems/3f444423-a92c-431f-8742-21463719172e
-- title:
--   Contracting the 47 profile pairs onto fifteen classes
-- statement:
--   The difference of the two connection probabilities on Hollom's hypergraph is the double sum $\sum_{\pi_0, \pi_1} \delta(\pi_0, \pi_1) W(\pi_0) W(\pi_1)$ over the $47 \times 47$ pairs of level profiles, where $\delta(\pi_0,\pi_1) = [0@0 \leftrightarrow 9@1] - [0@0 \leftrightarrow 9@0]$ and $W = $ `wFinal` is the profile weight. This statement evaluates that contraction.
--
--   The key structural fact is that the two levels interact **only** through the posts over $T = \{1, 6, 8\}$, so $\delta(\pi_0, \pi_1)$ depends on $\pi_1$ only through its restriction to $\{1, 6, 8, 9\}$. That restriction takes only $15$ values, so the $47$ level-$1$ profiles fall into $15$ classes, and the double sum collapses to $\sum_{k<15} (\mathtt{ck}\,k)(\mathtt{wk}\,k)$, where $\mathtt{wk}\,k$ is the total weight of class $k$ and $\mathtt{ck}\,k$ is the level-$0$ contraction $\sum_j \delta(\pi_j, k) W(\pi_j)$.
--
--   Fifteen products replace the $695$ pairs on which $\delta$ is nonzero, and fifteen is optimal for a bilinear decomposition: it is exactly the rank of the $47 \times 47$ integer matrix $\delta$.
-- source:
--   Gladkov, Pak, Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) no. 24, e2420725122; Section 3, Lemma 3.3 and Hollom's 3-uniform hypergraph (Fig. 1), with the path $\rho$ of Eq. [5].

import Definitions.Def_BunkbedTransferClasses
import Definitions.Def_BunkbedWZPoly
open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

theorem BunkbedTM.delta_contract (x y z u : Rat) :
    (∑ j : Fin 47, wFinal j x y z u *
       (∑ m : Fin 47, ((if glueConn (stFinal j) (stFinal m) 1 then (1 : ℚ) else 0)
          - (if glueConn (stFinal j) (stFinal m) 0 then (1 : ℚ) else 0)) * wFinal m x y z u))
      = ck0 x y z u * wk0 x y z u + ck1 x y z u * wk1 x y z u + ck2 x y z u * wk2 x y z u + ck3 x y z u * wk3 x y z u + ck4 x y z u * wk4 x y z u + ck5 x y z u * wk5 x y z u + ck6 x y z u * wk6 x y z u + ck7 x y z u * wk7 x y z u + ck8 x y z u * wk8 x y z u + ck9 x y z u * wk9 x y z u + ck10 x y z u * wk10 x y z u + ck11 x y z u * wk11 x y z u + ck12 x y z u * wk12 x y z u + ck13 x y z u * wk13 x y z u + ck14 x y z u * wk14 x y z u := by sorry
