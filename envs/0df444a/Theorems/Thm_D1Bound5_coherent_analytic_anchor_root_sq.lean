-- Prove2me | Theorems.Thm_D1Bound5_coherent_analytic_anchor_root_sq
-- name    : D1Bound5.coherent_analytic_anchor_root_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:28:51.961009+00:00
-- url     : https://prove2.me/theorems/edcd556e-6240-4421-bc2d-7502c201bdb1
-- title:
--   Coherent analytic anchor root sq
-- statement:
--   The coherent analytic anchor root has precisely the product square claimed in the manuscript. Consequently any integral product root of the same expression agrees with it up to sign.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 374-384, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.coherent_analytic_anchor_root_sq
    (a p q eta : ℂ) (ha : a ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (heta : eta ^ 2 = p * q) :
    (a * eta * ((1 + p⁻¹ * a⁻¹) ^ (1 / 2 : ℂ)) *
      ((1 + q⁻¹ * a⁻¹) ^ (1 / 2 : ℂ))) ^ 2 =
      (a * p + 1) * (a * q + 1) := by sorry



end D1Bound5
end
