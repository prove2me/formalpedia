-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_balanced_parameter_bounds
-- name    : CatalyticTreeEval.Main.balanced_parameter_bounds
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T02:35:23.962139+00:00
-- url     : https://prove2.me/theorems/5f444f63-497c-406c-a3f6-551969414e3f
-- title:
--   Balanced prime powers satisfy the product and dimension bounds
-- statement:
--   For distinct primes $p_i$ and positive $w$, the computable integer-root/logarithm exponent choice has product of prime powers greater than $w$. With $m=\prod_i p_i$ and $t$ the number of primes, its maximum prime power is at most $\lfloor(mw)^{1/t}\rfloor$. Consequently its binomial dimension is at most the cutoff dimension used in Theorem 3.10.
--
--   $$w<\prod_i p_i^{e_i},\qquad \Delta\le\lfloor(mw)^{1/t}\rfloor.$$
--
--   These numerical bounds justify the explicit balanced parameters independently of their native computation.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Theorem 3.10.

import Definitions.Def_CatalyticTreeEval_BalancedParameters

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem balanced_parameter_bounds {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : 0 < w) :
    w < ∏ i, p i ^ balancedExponents p w i ∧
    delta p (balancedExponents p w) ≤ ⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ ∧
    binomialDimension H (delta p (balancedExponents p w)) ≤
      binomialDimension H (⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ + 1) := by sorry

end CatalyticTreeEval.Main
