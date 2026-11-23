-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_factorial_add_eq_descFactorial_mul
-- name    : Formalism.CountingSumsFrames.factorial_add_eq_descFactorial_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:24.150345+00:00
-- url     : https://prove2.me/theorems/0967960c-d315-44ef-9c50-9535431cc83e
-- title:
--   Counting Sums Frames: factorial add eq desc Factorial mul
-- statement:
--   The Counting Sums Frames construction uses the factorial add eq desc Factorial mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L106-L109

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

theorem Formalism.CountingSumsFrames.factorial_add_eq_descFactorial_mul (a n : ℕ) : (a + n).factorial = (a + n).descFactorial n * a.factorial := by sorry
