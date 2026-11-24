-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_isF_monomial_frst
-- name    : Formalism.CountingSumsFrames.isF_monomial_frst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:24.930606+00:00
-- url     : https://prove2.me/theorems/495574ea-f867-4278-8259-88c4841cdc5e
-- title:
--   Counting Sums Frames: is F monomial frst
-- statement:
--   The Counting Sums Frames construction uses the is F monomial frst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L620-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L620-L625

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem Formalism.CountingSumsFrames.isF_monomial_frst (m : σ →₀ ℕ) (a : K) : IsF fs (monomial (frst fs m) a) := by sorry
