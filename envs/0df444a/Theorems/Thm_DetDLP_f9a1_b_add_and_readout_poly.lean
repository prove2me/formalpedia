-- Prove2me | Theorems.Thm_DetDLP_f9a1_b_add_and_readout_poly
-- name    : DetDLP.f9a1_b_add_and_readout_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T02:52:29.178637+00:00
-- url     : https://prove2.me/theorems/101b0b4b-671c-4e03-b0d6-4ffc4bf84793
-- title:
--   Polynomial-time residual scalar addition and zero-column readout
-- statement:
--   On canonical encodings, zipped addition modulo the coefficient modulus encodes the ring sum. Reading column zero of each row and dividing by the supplied power of two returns the encoded list of coefficient quotients. Both operations take polynomial time on arbitrary bit strings.

import Definitions.Def_DetDLP_F9A1_BAddRead
open Polynomial DetDLP DetDLP.F9A1 DetDLP.ResidualScalarOracle
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.f9a1_b_add_and_readout_poly :
    (∀ (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (x y : B f ell q),
      bAddRaw (Encoding.encodeList id [(2^q : ℕ).bits, bEncode f ell q hf x,
        bEncode f ell q hf y]) = bEncode f ell q hf (x + y)) ∧
    (∀ (f : ℤ[X]) (ell q g : ℕ) (hf : f.Monic) (acc : B f ell q)
      (zero : Fin f.natDegree), zero.val = 0 →
      bReadZeroDivRaw (Encoding.encodeList id [(2^g : ℕ).bits, List.replicate f.natDegree true,
        List.replicate ell true, bEncode f ell q hf acc]) =
        encodeNatListBin (List.ofFn fun j : Fin ell => word f ell q hf acc j zero / 2^g)) ∧
    (Groundwork.PolyT bAddRaw ∧ Groundwork.PolyT bReadZeroDivRaw) := by sorry
