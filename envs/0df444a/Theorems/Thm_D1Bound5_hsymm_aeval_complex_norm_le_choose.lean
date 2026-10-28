-- Prove2me | Theorems.Thm_D1Bound5_hsymm_aeval_complex_norm_le_choose
-- name    : D1Bound5.hsymm_aeval_complex_norm_le_choose
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:13.751989+00:00
-- url     : https://prove2.me/theorems/ca3b4171-b2f7-4a51-89c3-302b8da3ebe1
-- title:
--   Hsymm aeval complex norm le choose
-- statement:
--   Uniform exact-cardinality bound for complete homogeneous symmetric polynomials evaluated on a finite complex alphabet. No distinctness, nonzero-value or inhabitedness assumptions are required.
-- source:
--   D1Bound5/ComplexHsymmNorm.lean, lines 10-40, SHA-256 c7252d7667b324417f5f8a714dc25e995730949e38f38c8de4aa92481c81dc43. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.hsymm_aeval_complex_norm_le_choose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (k : ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ∀ i, ‖a i‖ ≤ ρ) :
    ‖MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ k)‖ ≤
      (Nat.choose (Fintype.card ι + k - 1) k : ℝ) * ρ ^ k := by sorry

end D1Bound5
end
