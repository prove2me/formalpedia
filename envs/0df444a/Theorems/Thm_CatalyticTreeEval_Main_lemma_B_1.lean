-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_lemma_B_1
-- name    : CatalyticTreeEval.Main.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:14.395952+00:00
-- url     : https://prove2.me/theorems/1f4fd8f0-bcaf-43d5-9748-b1e87173a39c
-- title:
--   Lemma B.1 — uniform canonical matching vectors
-- statement:
--   Let $p_1,\ldots,p_t$ be distinct input primes with $t\ge1$, let $e_i\ge0$, set $m=\prod_i p_i$, $q_i=p_i^{e_i}$ and $\delta=\max_iq_i$. If $H\ge w\ge1$ and $\prod_iq_i>w$, there is a canonical-set matching-vector family of size $N=\binom Hw$ and dimension
--
--   $$d=\sum_{j=0}^{\delta-1}\binom Hj.$$
--
--   A single finite machine prints the requested pair of vectors, including the supplied primes and exponents as input parameters, in space at most $C(1+\log_2N+\delta\log_2H+\log_2m)$ for a positive absolute constant. Both the machine and constant are chosen before the construction parameters. Zero exponents are included. This is the uniform matching construction underlying Theorem 3.10.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: O(log N+δ log H+log m) → C(1+log₂ N+δ log₂ H+log₂ m); reason: log₂ m is at least one, so the additive unit leaves the same uniform bound
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Lemma B.1, printed p. 36 (PDF p. 38); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem lemma_B_1 :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p e : Fin t → ℕ) (w H : ℕ),
      PrimeData p → 1 ≤ w → w ≤ H → w < ∏ i, p i ^ e i →
      ∃ U V : Fin (H.choose w) → Vec (modulus p) (binomialDimension H (delta p e)),
        SMatching (canonical p (modulus p)) U V ∧
        VectorAccess M (primeCode p ++ natsCode ((List.finRange t).map e ++ [w,H])) U V
          (C * (1 + log₂ (H.choose w) + delta p e * log₂ H + log₂ (modulus p))) := by sorry

end CatalyticTreeEval.Main
