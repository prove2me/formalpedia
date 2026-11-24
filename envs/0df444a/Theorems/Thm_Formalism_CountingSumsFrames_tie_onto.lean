-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_tie_onto
-- name    : Formalism.CountingSumsFrames.tie_onto
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:48.225863+00:00
-- url     : https://prove2.me/theorems/13d58276-21af-4316-a6e8-77d983f73a39
-- title:
--   Counting Sums Frames: tie onto
-- statement:
--   The Counting Sums Frames construction uses the tie onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1677-L1725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1677-L1725

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

theorem Formalism.CountingSumsFrames.tie_onto [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (μ : Fin r → ℤ)
    {v : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hv : v ∈ GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr) :
    ∃ f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      T.Ffull p (LL.setTies T n) i ρ (n i) f = v := by sorry
