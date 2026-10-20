-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_root_energy
-- name    : DerivativeChainPrivate.exists_root_energy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:42:54.844974+00:00
-- url     : https://prove2.me/theorems/d69d4734-b8e3-40f1-aa1e-d0db490aa5b5
-- title:
--   Actual polynomial predecessor energy inequality
-- statement:
--   Let P be a complex polynomial of positive degree and suppose P'(z)=0. There is an actual root a of P satisfying
--
--   $$|a-z|^2\le |a|^2-|z|^2.$$
--
--   There is no disk assumption, no simplicity assumption, and no external root-coupling premise. This is the polynomial one-step inequality used to build compatible chains.
-- source:
--   Derivative-zero chains: public formalization reference, R22, DerivativeChainPrivate.exists_root_energy. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChain_root_probability
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

theorem DerivativeChainPrivate.exists_root_energy (P : Polynomial ℂ) (hP : 0 < P.degree)
    (z : ℂ) (hz : P.derivative.eval z = 0) :
    ∃ a : ℂ, P.eval a = 0 ∧ ‖a - z‖ ^ 2 ≤ ‖a‖ ^ 2 - ‖z‖ ^ 2 := by sorry
