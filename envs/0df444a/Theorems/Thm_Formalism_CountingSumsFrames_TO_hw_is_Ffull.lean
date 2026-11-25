-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_hw_is_Ffull
-- name    : Formalism.CountingSumsFrames.TO.hw_is_Ffull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:32.106304+00:00
-- url     : https://prove2.me/theorems/c2f75282-eafe-4a6e-bc17-4735b3d768bd
-- title:
--   TO: hw is Ffull
-- statement:
--   The TO construction uses the hw is Ffull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2274-L2414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2274-L2414

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
include hρ

theorem Formalism.CountingSumsFrames.TO.hw_is_Ffull (μ : Fin r → ℤ) (v : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hv : v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr)
    (hw : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v) (hint : v ∈ IntPol p (Fin N × Fin r)) :
    ∃ f ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      v = T.Ffull p (LL.setTies T n) i ρ (n i) f := by sorry
