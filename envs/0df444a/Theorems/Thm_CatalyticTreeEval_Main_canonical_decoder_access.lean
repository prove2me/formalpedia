-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_canonical_decoder_access
-- name    : CatalyticTreeEval.Main.canonical_decoder_access
-- status  : Open
-- author  : @sragavan
-- created : 2026-11-14T02:18:07.068601+00:00
-- url     : https://prove2.me/theorems/a3f2ec08-259f-414d-8876-69c7fe1bfccd
-- title:
--   Uniform polynomial-time access to the explicit canonical decoder
-- statement:
--   There exist a single finite binary machine $M$, positive constants $C_s,C_t$, and a positive integer $q$, all fixed before the prime list. For every list of distinct odd primes, $m=\prod_i p_i$, decoder index $j<3^t$, and query residue $z$, the machine prints the two scalar fields of the already fixed canonical decoder. Its full addressed work prefix is at most $C_s\log_2m$ and its number of actual transitions is at most $C_t(1+\log_2m)^q$. The request uses exactly `decoderRequest (primeCode p) j.val z.val`, with the published binary encodings. This is the native computational obligation remaining in Lemma 3.19; no per-parameter machine, advice, assumed arithmetic oracle, or arbitrary enumeration is supplied.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3.4, Lemma 3.19.

import Definitions.Def_CatalyticTreeEval_DecoderCRT

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem canonical_decoder_access :
    ∃ (M : Machine) (Cs Ct : ℝ) (q : ℕ), 0 < Cs ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (t : ℕ) (p : Fin t → ℕ) (hp : OddPrimeData p),
        ∀ j z, PrintsIn M (decoderRequest (primeCode p) j.val z.val)
          (decoderOutput (DecoderConstruction.canonicalDecoder p hp.1) j z)
          (Cs * log₂ (modulus p)) (Ct * (1 + log₂ (modulus p)) ^ q) := by sorry

end CatalyticTreeEval.Main
