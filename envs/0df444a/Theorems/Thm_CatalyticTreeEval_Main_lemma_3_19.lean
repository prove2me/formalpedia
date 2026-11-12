-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_lemma_3_19
-- name    : CatalyticTreeEval.Main.lemma_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:52.01773+00:00
-- url     : https://prove2.me/theorems/ba9b469d-f60b-4ee2-b0c0-58a17e6f8d70
-- title:
--   Lemma 3.19 — canonical-sumset decoder
-- statement:
--   Let $p_1,\ldots,p_t$ be distinct odd input primes, with $t\ge1$ and product $m$. Let $S_m^*$ be the canonical score set and $A=S_m^*+S_m^*$. The two descriptions of $A$ agree:
--
--   $$z\in A\quad\Longleftrightarrow\quad z\bmod p_i\in\{0,1,2\}\quad\text{for every }i.$$
--
--   There is an $A$-decoder over $\mathbb Z/m\mathbb Z$ with sparsity $k\le3^t$. One finite machine outputs both $b_j$ and $\varphi_j(z)$ from the primes, term index and residue using space at most $C_s\log_2m$ and time at most $C_t(1+\log_2m)^q$. The positive constants and positive integer exponent are absolute and fixed before all primes and requests.
--
--   The decoder satisfies cancellation for every nonzero $a\in A$ and every mask $z$, and normalization only at zero. This supplies the sparse, ring-valued decoder required by the tree algorithm.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Lemma 3.19, printed p. 19 (PDF p. 21); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Decoder

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem lemma_3_19 :
    ∃ (M : Machine) (Cs Ct : ℝ) (q : ℕ), 0 < Cs ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (t : ℕ) (p : Fin t → ℕ), OddPrimeData p →
      ∃ (k : ℕ) (D : Decoder (modulus p) k), k ≤ 3 ^ t ∧
        (∀ z : ZMod (modulus p), z ∈ sumset (canonical p (modulus p)) ↔
          ∀ i, z.val % p i = 0 ∨ z.val % p i = 1 ∨ z.val % p i = 2) ∧
        IsDecoder (sumset (canonical p (modulus p))) D ∧
        (∀ j z, PrintsIn M (decoderRequest (primeCode p) j.val z.val)
          (decoderOutput D j z) (Cs * log₂ (modulus p))
          (Ct * (1 + log₂ (modulus p)) ^ q)) := by sorry

end CatalyticTreeEval.Main
