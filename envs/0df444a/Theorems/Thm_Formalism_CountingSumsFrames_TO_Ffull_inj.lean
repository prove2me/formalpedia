-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_Ffull_inj
-- name    : Formalism.CountingSumsFrames.TO.Ffull_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:27.134709+00:00
-- url     : https://prove2.me/theorems/654093d2-a176-4386-9b7b-e5e20396fbfe
-- title:
--   TO: Ffull inj
-- statement:
--   The TO construction uses the Ffull inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2213-L2222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2213-L2222

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

theorem Formalism.CountingSumsFrames.TO.Ffull_inj (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (h0 : T.Ffull p (LL.setTies T n) i ρ (n i) f = 0) : f = 0 := by sorry
