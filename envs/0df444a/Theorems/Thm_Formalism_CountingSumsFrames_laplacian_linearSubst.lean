-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_laplacian_linearSubst
-- name    : Formalism.CountingSumsFrames.laplacian_linearSubst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:47.19381+00:00
-- url     : https://prove2.me/theorems/18768b05-2c36-4429-a26b-7fac9b2abf15
-- title:
--   Counting Sums Frames: laplacian linear Subst
-- statement:
--   The Counting Sums Frames construction uses the laplacian linear Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L328-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L328-L344

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

theorem Formalism.CountingSumsFrames.laplacian_linearSubst (g : GL (Fin k) K) (f : PolXY K k) : ctrF K k (glAct g f) = glAct g (ctrF K k f) := by sorry
