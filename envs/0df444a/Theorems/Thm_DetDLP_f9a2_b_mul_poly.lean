-- Prove2me | Theorems.Thm_DetDLP_f9a2_b_mul_poly
-- name    : DetDLP.f9a2_b_mul_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T03:11:41.302005+00:00
-- url     : https://prove2.me/theorems/1235019f-ddfd-4154-aad8-9477d883a950
-- title:
--   Exact and uniform polynomial-time multiplication of residual scalar words
-- statement:
--   For any positive precision, truncation order and degree, and any monic integer polynomial of that degree, the wire multiplier sends the two canonical coefficient tables to the exact canonical table of the product in the doubly truncated algebra. The same wire function is polynomial-time for all choices of the parameters.
-- source:
--   DetDLP F9A2-v2, uniform multiplication wire specification

import Definitions.Def_DetDLP_F9A2_BMul
open Polynomial DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.f9a2_b_mul_poly :
    (∀ (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic), 0 < f.natDegree → 0 < ell → 0 < q →
      ∀ x y : ResidualScalarOracle.B f ell q,
        F9A2.bMulRaw (Encoding.encodeList id [(2^q : ℕ).bits, List.replicate ell true,
          List.replicate f.natDegree true,
          encodeNatListBin (List.ofFn fun i : Fin f.natDegree => ((f.coeff i.val : ZMod (2^q)).val)),
          encodeNatListBin (F9A2.flatten (ResidualScalarOracle.word f ell q hf x)),
          encodeNatListBin (F9A2.flatten (ResidualScalarOracle.word f ell q hf y))]) =
        encodeNatListBin (F9A2.flatten (ResidualScalarOracle.word f ell q hf (x*y)))) ∧
    Groundwork.PolyT F9A2.bMulRaw := by sorry
