-- Prove2me | Theorems.Thm_DetDLP_s8i_ec_moment_layout_wire_exists
-- name    : DetDLP.s8i_ec_moment_layout_wire_exists
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T03:05:25.006821+00:00
-- url     : https://prove2.me/theorems/ee6780a2-6e81-4c16-9d12-7cb98e7ee7c3
-- title:
--   EC moment layout wire exists
-- statement:
--   Sound $\exists$ wiring: for a fixed factor layout, some uniform address compiler encodes its subdivision on a tag-2 EC-moment word.
-- source:
--   DetDLP m8 sound ∃ packaging retry

import Definitions.Def_DetDLP_S8I_ECMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec

set_option autoImplicit false

namespace DetDLP

open S8C
open S8I.ECMoment
open S8G.FpMoment
open S8G.FpMoment.Code
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- For any fixed factor layout, some uniform address compiler wires that layout. -/

theorem s8i_ec_moment_layout_wire_exists
    (A : w3_FactorLayout) (test : w3_factorTest A)
    (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (j : Fin 4) (T : ℕ) (η : List Bool) :
    ∃ (a : Addresses) (_ : a.Uniform)
      (_ :
        make a (word E j T η) =
          encodeBTNInstance (word E j T η) (w3_factorGraph A).subdivision
            (scale (blockCount (bitLen p)) (bitLen p))
            (scale (blockCount (bitLen p)) (bitLen p)) 1)
      (_ :
        ∀ v a',
        port a (encodePortQuery (word E j T η) v.val (List.ofFn a')) =
          encodeNatListBin
            [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' then 1 else 0]),
      True := by sorry

end DetDLP
