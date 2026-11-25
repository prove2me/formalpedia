-- Prove2me | Theorems.Thm_DetDLP_s8h_ec_elem_layout_wire_exists
-- name    : DetDLP.s8h_ec_elem_layout_wire_exists
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T03:02:26.128981+00:00
-- url     : https://prove2.me/theorems/a3836474-3a6d-563d-94ce-46cd1c49d948
-- title:
--   EC elem layout wire exists
-- statement:
--   Sound $\exists$ wiring: for a fixed factor layout, some uniform address compiler encodes its subdivision on a tag-4 EC-element word.
-- source:
--   DetDLP m8 sound ∃ packaging retry

import Definitions.Def_DetDLP_S8H_ECElemGraph
import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec

set_option autoImplicit false

namespace DetDLP

open S8C
open S8H.ECElem
open S8G.FpMoment
open S8G.FpMoment.Code
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- For any fixed factor layout, some uniform address compiler wires that layout. -/

theorem s8h_ec_elem_layout_wire_exists
    (A : w3_FactorLayout) (test : w3_factorTest A)
    (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p)))
    (η : List Bool) :
    ∃ (a : Addresses) (_ : a.Uniform)
      (_ :
        make a (word E T S i η) =
          encodeBTNInstance (word E T S i η) (w3_factorGraph A).subdivision
            (scale (blockCount (bitLen p)) (bitLen p))
            (scale (blockCount (bitLen p)) (bitLen p)) 1)
      (_ :
        ∀ v a',
        port a (encodePortQuery (word E T S i η) v.val (List.ofFn a')) =
          encodeNatListBin
            [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' then 1 else 0]),
      True := by sorry

end DetDLP
