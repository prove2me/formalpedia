-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_coeff_diagMul_pow
-- name    : Formalism.CountingSumsFrames.coeff_diagMul_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:58.021222+00:00
-- url     : https://prove2.me/theorems/f63e6541-62c0-4beb-8a97-6825eec4336c
-- title:
--   Counting Sums Frames: coeff diag Mul pow
-- statement:
--   The Counting Sums Frames construction uses the coeff diag Mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L140-L142

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

theorem Formalism.CountingSumsFrames.coeff_diagMul_pow (i : Fin k) (n : ℕ) (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m ((h3e K i ^ n) f) = if h3s i n ≤ m then coeff (m - h3s i n) f else 0 := by sorry
