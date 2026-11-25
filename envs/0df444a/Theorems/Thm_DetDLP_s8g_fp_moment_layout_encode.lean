-- Prove2me | Theorems.Thm_DetDLP_s8g_fp_moment_layout_encode
-- name    : DetDLP.s8g_fp_moment_layout_encode
-- status  : Disproved
-- author  : @Bingsheng
-- created : 2026-11-24T19:20:28.061537+00:00
-- url     : https://prove2.me/theorems/621f78e2-fec8-46de-be8c-5ef35328d982
-- title:
--   DetDLP s8g fp moment layout encode
-- statement:
--   `make`/`port` alignment for tag-1 moment layouts.
--
--   $$
--   \text{Open child for Stage I layout decomposition (Formal Paper Thm.\,3.1).}
--   $$
-- source:
--   Liu–Zhang–Ren Formal Paper, Theorem 3.1 (Stage I query layouts)

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec

set_option autoImplicit false

namespace DetDLP

open S8C
open S8G.FpMoment
open S8G.FpMoment.Code
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- `make`/`port` for a uniform address map agree with the factor-graph subdivision. -/
theorem s8g_fp_moment_layout_encode (a : Addresses) (ha : a.Uniform)
    (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool) (A : w3_FactorLayout)
    (test : w3_factorTest A) :
    ∃ (build :
        make a (word p j T η) =
          encodeBTNInstance (word p j T η) (w3_factorGraph A).subdivision
            (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
      (eval :
        ∀ v a',
        port a (encodePortQuery (word p j T η) v.val (List.ofFn a')) =
          encodeNatListBin
            [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' then 1 else 0]) ,
    True := by sorry

end DetDLP
