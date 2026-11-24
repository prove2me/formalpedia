-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_finrank_MMw
-- name    : Formalism.CountingSumsFrames.finrank_MMw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:41.521693+00:00
-- url     : https://prove2.me/theorems/c5406b52-e79d-4038-aa63-dc28335c201a
-- title:
--   Counting Sums Frames: finrank MMw
-- statement:
--   The Counting Sums Frames construction uses the finrank MMw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1767-L1791
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1767-L1791

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

theorem Formalism.CountingSumsFrames.finrank_MMw [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (w : Fin r → ℤ) :
    Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) =
      Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) := by sorry
