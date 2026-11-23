-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_linearSubst_pairing
-- name    : Formalism.CountingSumsFrames.linearSubst_pairing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:16.964789+00:00
-- url     : https://prove2.me/theorems/946ad838-5944-4bee-a8a1-f3f90df97074
-- title:
--   Counting Sums Frames: linear Subst pairing
-- statement:
--   The Counting Sums Frames construction uses the linear Subst pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L267-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L267-L283

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

theorem Formalism.CountingSumsFrames.linearSubst_pairing (g : GL (Fin k) K) : glAct g (hXY K k) = hXY K k := by sorry
