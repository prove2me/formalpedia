-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row_natDegree
-- name    : DerivativeChainPrivate.row_natDegree
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:45:26.620982+00:00
-- url     : https://prove2.me/theorems/df4c35f2-0374-4893-8be9-8311fe20222b
-- title:
--   Natural degree of each actual derivative row
-- statement:
--   For natural numbers m<=n and a list of n complex root slots a_i, form the monic product p(X)=product_i(X-a_i). Its derivative row of order n-m has natural degree m:
--
--   $$\operatorname{natDegree}(p^{(n-m)})=m.$$
--
--   Repeated roots are allowed. The empty root list and m=n=0 are included. This identifies the nonconstant rows used by complete chains.
-- source:
--   Derivative-zero chains: public formalization reference, R24, DerivativeChainPrivate.row_natDegree. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate

theorem DerivativeChainPrivate.row_natDegree {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    (row a m).natDegree = m := by sorry
