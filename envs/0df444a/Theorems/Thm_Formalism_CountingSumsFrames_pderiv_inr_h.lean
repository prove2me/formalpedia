-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pderiv_inr_h
-- name    : Formalism.CountingSumsFrames.pderiv_inr_h
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:56.445791+00:00
-- url     : https://prove2.me/theorems/7d888365-8f0f-4904-9e61-a2aba84a2377
-- title:
--   Counting Sums Frames: pderiv inr h
-- statement:
--   The Counting Sums Frames construction uses the pderiv inr h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PairingAdjointLaplacianHolds.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PairingAdjointLaplacianHolds.lean#L30-L32

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable (K : Type) [Field K] (k : ℕ)
variable {K k}

theorem Formalism.CountingSumsFrames.pderiv_inr_h (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by sorry
