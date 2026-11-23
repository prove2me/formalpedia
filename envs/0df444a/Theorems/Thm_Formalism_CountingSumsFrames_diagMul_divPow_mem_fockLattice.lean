-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_diagMul_divPow_mem_fockLattice
-- name    : Formalism.CountingSumsFrames.diagMul_divPow_mem_fockLattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:14.727806+00:00
-- url     : https://prove2.me/theorems/0dc0ccca-59c9-46a8-bcb0-3b27e2651050
-- title:
--   Counting Sums Frames: diag Mul div Pow mem fock Lattice
-- statement:
--   The Counting Sums Frames construction uses the diag Mul div Pow mem fock Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L217-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L217-L231

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem Formalism.CountingSumsFrames.diagMul_divPow_mem_fockLattice (R : Subring K) (i : Fin k) (n : ℕ) (f : PolXY K k) (hf : f ∈ FockLat R) :
    (((n.factorial : K)⁻¹) • h3e K i ^ n) f ∈ FockLat R := by sorry
