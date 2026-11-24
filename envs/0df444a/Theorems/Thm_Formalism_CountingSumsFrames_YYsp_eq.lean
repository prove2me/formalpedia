-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_YYsp_eq
-- name    : Formalism.CountingSumsFrames.YYsp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:08.985387+00:00
-- url     : https://prove2.me/theorems/d0abb451-0938-40d5-b9ee-beeec3e65a25
-- title:
--   Counting Sums Frames: YYsp eq
-- statement:
--   The Counting Sums Frames construction uses the YYsp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1795-L1801
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1795-L1801

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

theorem Formalism.CountingSumsFrames.YYsp_eq [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.YYsp p LL i ρ n f = YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
      (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by sorry
