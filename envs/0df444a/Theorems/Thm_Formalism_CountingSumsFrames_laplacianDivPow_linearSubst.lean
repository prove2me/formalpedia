-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_laplacianDivPow_linearSubst
-- name    : Formalism.CountingSumsFrames.laplacianDivPow_linearSubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:01.47521+00:00
-- url     : https://prove2.me/theorems/811aa827-8b71-45da-859b-351eaccffb72
-- title:
--   Counting Sums Frames: laplacian Div Pow linear Subst
-- statement:
--   The Counting Sums Frames construction uses the laplacian Div Pow linear Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L356-L358

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

theorem Formalism.CountingSumsFrames.laplacianDivPow_linearSubst (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) :
    ctrDiv K k l (glAct g f) = glAct g (ctrDiv K k l f) := by sorry
