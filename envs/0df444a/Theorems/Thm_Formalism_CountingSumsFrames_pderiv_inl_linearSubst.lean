-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pderiv_inl_linearSubst
-- name    : Formalism.CountingSumsFrames.pderiv_inl_linearSubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:50.058821+00:00
-- url     : https://prove2.me/theorems/d936f06f-a81e-4f40-b3f6-049862976714
-- title:
--   Counting Sums Frames: pderiv inl linear Subst
-- statement:
--   The Counting Sums Frames construction uses the pderiv inl linear Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L306-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L306-L313

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

theorem Formalism.CountingSumsFrames.pderiv_inl_linearSubst (g : GL (Fin k) K) (j : Fin k) (f : PolXY K k) :
    pderiv (Sum.inl j) (glAct g f) =
      ∑ i : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * glAct g (pderiv (Sum.inl i) f) := by sorry
