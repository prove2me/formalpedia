-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_diagLaplacian_apply
-- name    : Formalism.CountingSumsFrames.diagLaplacian_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:01.032892+00:00
-- url     : https://prove2.me/theorems/d89bdc24-331c-4003-b800-cef946aefeb7
-- title:
--   Counting Sums Frames: diag Laplacian apply
-- statement:
--   The Counting Sums Frames construction uses the diag Laplacian apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L131-L132

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

theorem Formalism.CountingSumsFrames.diagLaplacian_apply (i : Fin k) (f : PolXY K k) :
    h3d K i f = pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by sorry
