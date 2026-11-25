-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_Ffull
-- name    : Formalism.CountingSumsFrames.TO.phi_Ffull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:50.442384+00:00
-- url     : https://prove2.me/theorems/8124cfa8-88df-4323-a040-70f79677df95
-- title:
--   TO: phi Ffull
-- statement:
--   The TO construction uses the phi Ffull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1621-L1645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1621-L1645

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm

theorem Formalism.CountingSumsFrames.TO.phi_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f) =
      rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))
        (tiePhiAt p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (Fin.castSucc (Fin.last (T.pos i)))
          (Fin.last (T.pos i + 1)) (T.z i) (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)) := by sorry
