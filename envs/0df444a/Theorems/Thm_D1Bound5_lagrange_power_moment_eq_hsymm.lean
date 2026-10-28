-- Prove2me | Theorems.Thm_D1Bound5_lagrange_power_moment_eq_hsymm
-- name    : D1Bound5.lagrange_power_moment_eq_hsymm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:15.735364+00:00
-- url     : https://prove2.me/theorems/06dfb4d6-6b73-4686-859c-492f8886cd60
-- title:
--   Lagrange power moment eq hsymm
-- statement:
--   All-order Lagrange moments equal mathlib's complete homogeneous symmetric polynomials, with no nonzero-node restriction.
-- source:
--   D1Bound5/LagrangeHomogeneous.lean, lines 103-113, SHA-256 b4a9130e2e09325e0a7c90a60c13433e1e3d45746589329d45719e084b45b442. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Polynomial Finset

namespace D1Bound5










theorem _root_.D1Bound5.lagrange_power_moment_eq_hsymm
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, (a i) ^ (s.card - 1 + k) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      MvPolynomial.aeval (fun i : s => a i) (MvPolynomial.hsymm s F k) := by sorry

end D1Bound5
end
