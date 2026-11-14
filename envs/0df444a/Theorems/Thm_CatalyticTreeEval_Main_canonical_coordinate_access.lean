-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_canonical_coordinate_access
-- name    : CatalyticTreeEval.Main.canonical_coordinate_access
-- status  : Open
-- author  : @sragavan
-- created : 2026-11-14T02:35:32.945866+00:00
-- url     : https://prove2.me/theorems/6f28210d-2f78-48d1-b7ad-aa48c30cba28
-- title:
--   Uniform native access to explicitly indexed canonical matching vectors
-- statement:
--   There are one finite binary machine and a positive constant $C$, fixed before every prime list and parameter choice, that choose actual subset and square-free monomial indexings and print the coordinates of the fixed coefficient/evaluation construction. For $1\le w\le H$ and $w<\prod_i p_i^{e_i}$, the addressed workspace is
--
--   $$C\left(1+\log_2\binom Hw+\Delta\log_2H+\log_2m\right).$$
--
--   The input contains the primes, exponents, $w$ and $H$ with the mission encodings. The native printing predicate includes finite-table halting and the full trajectory workspace bound. This retains the computational content of Lemma B.1 rather than supplying an unrelated existential family.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.1.

import Definitions.Def_CatalyticTreeEval_CanonicalCoordinates

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem canonical_coordinate_access :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p e : Fin t → ℕ) (w H : ℕ) (hp : PrimeData p),
      1 ≤ w → w ≤ H → w < ∏ i, p i ^ e i →
      ∃ I : CanonicalIndexing H w (delta p e),
        VectorAccess M (primeCode p ++ natsCode ((List.finRange t).map e ++ [w,H]))
          (canonicalCoefficientVectors p e hp w H I) (canonicalEvaluationVectors p e w H I)
          (C * (1 + log₂ (H.choose w) + delta p e * log₂ H + log₂ (modulus p))) := by sorry

end CatalyticTreeEval.Main
