-- Prove2me | Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
-- name    : D1Bound5.coherent_analytic_terminal_root_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:47.918575+00:00
-- url     : https://prove2.me/theorems/e4fa031a-6c97-407f-8717-6f5c2435f45b
-- title:
--   Coherent analytic terminal root sq
-- statement:
--   The chosen coherent terminal root has square `pq + 1`, for either choice of the square root `eta` of `pq`.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 365-372, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset Polynomial

namespace D1Bound5













end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5




theorem _root_.D1Bound5.coherent_analytic_terminal_root_sq
    (p q eta : ℂ) (hp : p ≠ 0) (hq : q ≠ 0)
    (heta : eta ^ 2 = p * q) :
    (eta * ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))) ^ 2 = p * q + 1 := by sorry





end D1Bound5
end
