-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_tieF_rename
-- name    : Formalism.CountingSumsFrames.TO.tieF_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:54.14454+00:00
-- url     : https://prove2.me/theorems/e71de66a-f8c1-40e3-a0f6-eee45c07a617
-- title:
--   TO: tie F rename
-- statement:
--   The TO construction uses the tie F rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1445-L1449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1445-L1449

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

theorem Formalism.CountingSumsFrames.TO.tieF_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieF w e F) := by sorry
