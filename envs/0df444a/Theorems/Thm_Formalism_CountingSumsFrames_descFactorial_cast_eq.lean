-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_descFactorial_cast_eq
-- name    : Formalism.CountingSumsFrames.descFactorial_cast_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:50.51639+00:00
-- url     : https://prove2.me/theorems/e1e97d73-f4a0-4eab-9254-8dab9988c6eb
-- title:
--   Counting Sums Frames: desc Factorial cast eq
-- statement:
--   The Counting Sums Frames construction uses the desc Factorial cast eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L198-L200

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

theorem Formalism.CountingSumsFrames.descFactorial_cast_eq (a n : ℕ) :
    (((a + n).descFactorial n : ℕ) : K) = (n.factorial : K) * (((a + n).choose n : ℕ) : K) := by sorry
