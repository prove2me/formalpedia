-- Prove2me | Theorems.Thm_D1Bound5_coherent_weighted_remainder_summable_and_norm_le
-- name    : D1Bound5.coherent_weighted_remainder_summable_and_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:48.179717+00:00
-- url     : https://prove2.me/theorems/85b8dd64-b804-4fa5-a2b4-78a07bfd5b97
-- title:
--   Coherent weighted remainder summable and norm le
-- statement:
--   An analytic coefficient envelope, together with the exact positive-degree homogeneous majorant, controls the entire square-root interpolation tail. This is a conditional interface: the bound on the coefficients `f` must be proved separately for the specific square-root convolution.
-- source:
--   D1Bound5/CoherentWeightedRemainder.lean, lines 5-84, SHA-256 2758a368bb264ac87ab368841c49c3a14a5ce140db6a7ea9c1e62cd97457ff48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
namespace D1Bound5


theorem _root_.D1Bound5.coherent_weighted_remainder_summable_and_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (f : ℕ → ℂ) (m : ℕ) (C ρ t : ℝ)
    (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (ht0 : 0 ≤ t)
    (hρ : ∀ i, ‖a i‖ ≤ ρ) (hradius : ρ * t < 1)
    (hf : ∀ j : ℕ, ‖f (m + (j + 1))‖ ≤ C * t ^ (m + (j + 1))) :
    Summable (fun j : ℕ => f (m + (j + 1)) *
       MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))) ∧
    ‖∑' j : ℕ, f (m + (j + 1)) *
       MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ ≤
      C * t ^ m * (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by sorry

end D1Bound5
end
