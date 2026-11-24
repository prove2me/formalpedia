-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_monomial_eq_basis
-- name    : Formalism.CountingSumsFrames.monomial_eq_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:28.994292+00:00
-- url     : https://prove2.me/theorems/8668c835-67ea-4a1c-b570-0bc9995a03ac
-- title:
--   Counting Sums Frames: monomial eq basis
-- statement:
--   The Counting Sums Frames construction uses the monomial eq basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L527-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L527-L528

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

theorem Formalism.CountingSumsFrames.monomial_eq_basis (m : σ →₀ ℕ) (a : K) : monomial m a = a • (basisMonomials σ K) m := by sorry
