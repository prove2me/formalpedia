-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_tie_into
-- name    : Formalism.CountingSumsFrames.tie_into
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:17.013933+00:00
-- url     : https://prove2.me/theorems/b3284738-6b50-4c7e-888a-745995218881
-- title:
--   Counting Sums Frames: tie into
-- statement:
--   The Counting Sums Frames construction uses the tie into property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1727-L1741
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1727-L1741

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
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm

theorem Formalism.CountingSumsFrames.tie_into [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (w : Fin r → ℤ)
    {f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]}
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈
      GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by sorry
