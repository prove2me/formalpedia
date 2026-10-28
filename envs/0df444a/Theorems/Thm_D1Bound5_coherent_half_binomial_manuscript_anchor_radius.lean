-- Prove2me | Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_anchor_radius
-- name    : D1Bound5.coherent_half_binomial_manuscript_anchor_radius
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:11:54.52099+00:00
-- url     : https://prove2.me/theorems/febd33ac-df81-415d-96ad-88af410bd26e
-- title:
--   Coherent half binomial manuscript anchor radius
-- statement:
--   The manuscript's size assumptions place every anchor evaluation strictly inside the disk of convergence of the half-binomial series.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 329-349, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.coherent_half_binomial_manuscript_anchor_radius
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (x : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P)
    (ha : ∀ i ∈ s, A ≤ ‖a i‖)
    (hx : ‖x‖ ≤ 1 / P) (hAP : 1 < A * P) :
    ∀ i ∈ s, ‖x * (a i)⁻¹‖ < 1 := by sorry

end D1Bound5




namespace D1Bound5









end D1Bound5
end
