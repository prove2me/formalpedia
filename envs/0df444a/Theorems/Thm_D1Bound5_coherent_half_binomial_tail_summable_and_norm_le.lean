-- Prove2me | Theorems.Thm_D1Bound5_coherent_half_binomial_tail_summable_and_norm_le
-- name    : D1Bound5.coherent_half_binomial_tail_summable_and_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:28.591404+00:00
-- url     : https://prove2.me/theorems/1c81a922-b922-42e2-a86d-6d73e3ab8718
-- title:
--   Coherent half binomial tail summable and norm le
-- statement:
--   The actual complex half-binomial convolution satisfies the complete weighted-homogeneous tail bound. The coefficient envelope is proved here, rather than inserted as an independent hypothesis.
-- source:
--   D1Bound5/ComplexHalfBinomial.lean, lines 77-101, SHA-256 e7e6f8b11a6f554af427f9bfa36df35a8240f67bed0729f2ba7396a3dc39d624. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5








theorem _root_.D1Bound5.coherent_half_binomial_tail_summable_and_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (x y : ℂ) (m : ℕ) (ρ t : ℝ)
    (hm : 1 ≤ m) (hρ0 : 0 ≤ ρ) (ht : 0 ≤ t)
    (ha : ∀ i, ‖a i‖ ≤ ρ)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (hradius : ρ * t < 1) :
    Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (m + (j + 1)) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))) ∧
    ‖∑' j : ℕ, halfBinomialWeightedCoeff x y (m + (j + 1)) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ ≤
      (4 * |halfBinomialCoeff (m + 1)|) * t ^ m *
        (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by sorry

end D1Bound5
end
