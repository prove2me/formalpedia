-- Prove2me | Theorems.Thm_DetDLP_f9a3_b_unpack_term_poly
-- name    : DetDLP.f9a3_b_unpack_term_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T02:54:24.491966+00:00
-- url     : https://prove2.me/theorems/ca4af6aa-ec3a-4f0e-b64d-efdfb5895926
-- title:
--   Polynomial-time bit unpacking of a residual summand
-- statement:
--   Residual scalar unpacking splits as a sum indexed by digit assignments. For a monic defining polynomial of positive degree, the six-field bit decoder recovers precisely the canonical coefficient words of each summand, in row-major order, and computes them in polynomial time.

import Definitions.Def_DetDLP_F9A3_BUnpackTerm
open Polynomial Finset DetDLP DetDLP.ResidualScalarOracle OAI.Algorithms.SubexponentialSAT

theorem DetDLP.f9a3_b_unpack_term_poly :
    (∀ (f : ℤ[X]) (ell q : ℕ) (G : BipartiteMultigraph) (h J : ℕ)
       (d : (Fin G.nV → Fin J) → Fin (spacing f G * ell) → ℕ),
       ∑ a, unpackTerm f ell q G h a (d a) = unpack f ell q G h J d) ∧
    (∀ (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (_ : 0 < f.natDegree)
       (G : BipartiteMultigraph) (h J : ℕ) (a : Fin G.nV → Fin J)
       (d_a : Fin (spacing f G * ell) → ℕ),
       bUnpackTermRaw (Encoding.encodeList id [(2^q : ℕ).bits,
         (2^(h * ∑ v, (a v).val) % 2^q : ℕ).bits, List.replicate ell true,
         List.replicate (spacing f G) true, encodeNatListBin (fCoeffs f q),
         encodeNatListBin (List.ofFn d_a)]) =
       encodeNatListBin (List.ofFn fun idx : Fin (ell * f.natDegree) =>
         word f ell q hf (unpackTerm f ell q G h a d_a)
           (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2)) ∧
    Groundwork.PolyT bUnpackTermRaw := by sorry
