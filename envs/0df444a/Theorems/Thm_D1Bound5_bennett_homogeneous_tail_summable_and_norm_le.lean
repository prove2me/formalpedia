-- Prove2me | Theorems.Thm_D1Bound5_bennett_homogeneous_tail_summable_and_norm_le
-- name    : D1Bound5.bennett_homogeneous_tail_summable_and_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:42.090129+00:00
-- url     : https://prove2.me/theorems/80aba9a1-85e2-41ef-b8d2-755e9b59ec63
-- title:
--   Bennett homogeneous tail summable and norm le
-- statement:
--   A fully explicit generalized-binomial/homogeneous tail is summable and satisfies the sharp negative-binomial majorant. Here the repeated-node count is n+1, as required for a denominator of degree n+1.
-- source:
--   D1Bound5/BennettResidualMajorant.lean, lines 66-137, SHA-256 b75484763e5bdb67dae9e19c0cad718baf723c8291fc2f17c55a13171ba3db40. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
An elementary analytic majorant for the actual binomial/homogeneous tail that
arises in Bennett's simultaneous approximants.  In contrast to a coefficient
envelope interface, every coefficient of the series below is specified.

The algebraic identification of the residue moments with homogeneous
polynomials is a separate theorem.  This file does not assume that an arbitrary
series is a Bennett residual.  Once that identification is available, the
specialization n = 3k, s = k + 1/2 gives exactly the eta exponent in the paper.
-/

namespace D1Bound5










theorem _root_.D1Bound5.bennett_homogeneous_tail_summable_and_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (n : ℕ) (s ρ : ℝ) (x : ℂ)
    (hcard : Fintype.card ι = n + 1)
    (hs : s < n) (hρ0 : 0 ≤ ρ)
    (ha : ∀ i, ‖a i‖ ≤ ρ) (hradius : ρ * ‖x‖ < 1) :
    Summable (fun t : ℕ =>
      (Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)) ∧
    ‖∑' t : ℕ, (Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖ ≤
      |Ring.choose s n| * ‖x‖ ^ n / (1 - ρ * ‖x‖) ^ ((n : ℝ) - s) := by sorry



end D1Bound5
end
