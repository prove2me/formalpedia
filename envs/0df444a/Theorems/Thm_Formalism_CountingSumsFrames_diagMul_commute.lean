-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_diagMul_commute
-- name    : Formalism.CountingSumsFrames.diagMul_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:06.886732+00:00
-- url     : https://prove2.me/theorems/2c53601f-64b5-4b71-b70b-8c52baa92591
-- title:
--   Counting Sums Frames: diag Mul commute
-- statement:
--   The Counting Sums Frames construction uses the diag Mul commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L165-L168

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

theorem Formalism.CountingSumsFrames.diagMul_commute (i j : Fin k) : Commute (h3e K i) (h3e K j) := by sorry
