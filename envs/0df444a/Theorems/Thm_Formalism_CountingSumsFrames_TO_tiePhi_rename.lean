-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_tiePhi_rename
-- name    : Formalism.CountingSumsFrames.TO.tiePhi_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:06.659802+00:00
-- url     : https://prove2.me/theorems/a755ada6-d487-4588-9cea-7de4a71cd75f
-- title:
--   TO: tie Phi rename
-- statement:
--   The TO construction uses the tie Phi rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1451-L1472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1451-L1472

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
variable {k σ : Type} [Field k]

theorem Formalism.CountingSumsFrames.TO.tiePhi_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ) (o n z : ℕ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tiePhi (fun c => ι (w c)) (fun c => ι (e c)) o n z (rename ι F) =
      rename ι (Formalism.GM.tiePhi w e o n z F) := by sorry
