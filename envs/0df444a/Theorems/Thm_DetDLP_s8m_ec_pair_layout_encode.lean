-- Prove2me | Theorems.Thm_DetDLP_s8m_ec_pair_layout_encode
-- name    : DetDLP.s8m_ec_pair_layout_encode
-- status  : Disproved
-- author  : @Bingsheng
-- created : 2026-11-24T19:20:22.223216+00:00
-- url     : https://prove2.me/theorems/8393aedf-a827-4b4c-b40e-1708e50dcd4d
-- title:
--   DetDLP s8m ec pair layout encode
-- statement:
--   `make`/`port` alignment for EC pair layouts.
--
--   $$
--   \text{Open child for Stage I layout decomposition (Formal Paper Thm.\,3.1).}
--   $$
-- source:
--   Liu–Zhang–Ren Formal Paper, Theorem 3.1 (Stage I query layouts)

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec

set_option autoImplicit false

namespace DetDLP

open S8C
open S8M.ECPair
open S8M.ECPair.Packet
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Wired `make`/`port` for EC pair queries match the factor subdivision. -/
theorem s8m_ec_pair_layout_encode (a : S8G.FpMoment.Code.Addresses) (ha : a.Uniform)
    (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool)
    (A : w3_FactorLayout) (test : w3_factorTest A) :
    ∃ (build :
        make a (word E T S X η) =
          encodeBTNInstance (word E T S X η) (w3_factorGraph A).subdivision
            (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
      (eval :
        ∀ v a',
        port a (encodePortQuery (word E T S X η) v.val (List.ofFn a')) =
          encodeNatListBin
            [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' then 1 else 0]) ,
    True := by sorry

end DetDLP
