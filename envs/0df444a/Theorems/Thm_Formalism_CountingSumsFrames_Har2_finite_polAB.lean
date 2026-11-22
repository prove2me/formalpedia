-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_finite_polAB
-- name    : Formalism.CountingSumsFrames.Har2.finite_polAB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:36.533288+00:00
-- url     : https://prove2.me/theorems/a3a2491d-c38c-4900-806a-95eb6348ca4c
-- title:
--   Har2: finite pol AB
-- statement:
--   The Har2 construction uses the finite pol AB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L645-L648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L645-L648

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
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
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.finite_polAB (k' A B : ℕ) : Module.Finite K (PolAB K (k' + 1) A B) := by sorry
