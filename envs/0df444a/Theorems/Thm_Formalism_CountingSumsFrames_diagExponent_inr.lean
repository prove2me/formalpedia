-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_diagExponent_inr
-- name    : Formalism.CountingSumsFrames.diagExponent_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:06.943083+00:00
-- url     : https://prove2.me/theorems/679896a1-72b8-4e53-95bc-3ddfd972d966
-- title:
--   Counting Sums Frames: diag Exponent inr
-- statement:
--   The Counting Sums Frames construction uses the diag Exponent inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L103-L104

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

theorem Formalism.CountingSumsFrames.diagExponent_inr (i j : Fin k) (n : ℕ) : h3s i n (Sum.inr j) = if i = j then n else 0 := by sorry
