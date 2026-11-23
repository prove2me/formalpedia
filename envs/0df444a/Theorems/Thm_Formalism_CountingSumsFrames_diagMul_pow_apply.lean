-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_diagMul_pow_apply
-- name    : Formalism.CountingSumsFrames.diagMul_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:17.68463+00:00
-- url     : https://prove2.me/theorems/6a8a5a2f-08be-48af-bbe2-dfe3647eb1b0
-- title:
--   Counting Sums Frames: diag Mul pow apply
-- statement:
--   The Counting Sums Frames construction uses the diag Mul pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L134-L138

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

theorem Formalism.CountingSumsFrames.diagMul_pow_apply (i : Fin k) (n : ℕ) (f : PolXY K k) :
    (h3e K i ^ n) f = monomial (h3s i n) (1 : K) * f := by sorry
