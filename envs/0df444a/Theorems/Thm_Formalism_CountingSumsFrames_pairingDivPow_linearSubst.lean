-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pairingDivPow_linearSubst
-- name    : Formalism.CountingSumsFrames.pairingDivPow_linearSubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:36.485966+00:00
-- url     : https://prove2.me/theorems/9fb30d9c-7783-4a8b-8e9b-bc5ba2f624a1
-- title:
--   Counting Sums Frames: pairing Div Pow linear Subst
-- statement:
--   The Counting Sums Frames construction uses the pairing Div Pow linear Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L346-L348

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

theorem Formalism.CountingSumsFrames.pairingDivPow_linearSubst (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) :
    hDiv K k l (glAct g f) = glAct g (hDiv K k l f) := by sorry
