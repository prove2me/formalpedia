-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ctrF_apply
-- name    : Formalism.CountingSumsFrames.ctrF_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:59.42283+00:00
-- url     : https://prove2.me/theorems/37d443de-3e15-47a7-9c67-8ef27a51259d
-- title:
--   Counting Sums Frames: ctr F apply
-- statement:
--   The Counting Sums Frames construction uses the ctr F apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PairingAdjointLaplacianHolds.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PairingAdjointLaplacianHolds.lean#L22-L24

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

theorem Formalism.CountingSumsFrames.ctrF_apply (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by sorry
