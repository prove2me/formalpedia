-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_composite_weight_detector_print
-- name    : CatalyticTreeEval.Main.composite_weight_detector_print
-- status  : Open
-- author  : @sragavan
-- created : 2026-11-14T02:01:21.322543+00:00
-- url     : https://prove2.me/theorems/fec05b55-4f63-4d4d-a115-ccd9fd2ee189
-- title:
--   Uniform logarithmic-space sparse printer for the composite detector
-- statement:
--   There are one native binary machine and a positive constant $C$, fixed before every prime list and parameter choice, that print the sparse code of the explicit CRT detector. For distinct primes $p_i$, $1\le w\le H$ and $w<\prod_i p_i^{e_i}$, the addressed work space is bounded by
--
--   $$C\bigl(\Delta\log_2 H+\log_2 m\bigr),\qquad m=\prod_i p_i,\quad \Delta=\max_i p_i^{e_i}.$$
--
--   The input contains the encoded prime list, exponents, $w$ and $H$. Printing is the native finite-transition-table predicate from the mission, including halting and the full trajectory workspace bound. Together with the algebraic properties this gives the exact uniform construction required in Corollary B.6.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Corollary B.6.

import Definitions.Def_CatalyticTreeEval_CompositeDetector

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem composite_weight_detector_print :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p e : Fin t → ℕ) (w H : ℕ) (hp : PrimeData p),
      1 ≤ w → w ≤ H → w < ∏ i, p i ^ e i →
        PolyPrint M (primeCode p ++ natsCode ((List.finRange t).map e ++ [w,H]))
          (compositeWeightDetector p e hp w H)
          (C * (delta p e * log₂ H + log₂ (modulus p))) := by sorry

end CatalyticTreeEval.Main
