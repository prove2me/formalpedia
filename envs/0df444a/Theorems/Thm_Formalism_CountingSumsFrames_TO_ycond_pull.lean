-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ycond_pull
-- name    : Formalism.CountingSumsFrames.TO.ycond_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:31.091807+00:00
-- url     : https://prove2.me/theorems/dc29720b-fab2-487b-9a97-4f801632ea0f
-- title:
--   TO: ycond pull
-- statement:
--   The TO construction uses the ycond pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2243-L2270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2243-L2270

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
omit hS

theorem Formalism.CountingSumsFrames.TO.ycond_pull (J : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p])
    (h : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) F ∈ YCond p LL J M) :
    F ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by sorry
