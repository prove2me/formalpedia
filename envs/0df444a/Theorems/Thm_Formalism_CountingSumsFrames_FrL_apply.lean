-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_FrL_apply
-- name    : Formalism.CountingSumsFrames.FrL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:04.910394+00:00
-- url     : https://prove2.me/theorems/085087b7-7fa7-4bcc-baa0-0f0b5c03a8a1
-- title:
--   Counting Sums Frames: Fr L apply
-- statement:
--   The Counting Sums Frames construction uses the Fr L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1759-L1760
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1759-L1760

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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.FrL_apply [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n0 : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : FrL p L T i ρ n0 f = T.Ffull p L i ρ n0 f := by sorry
