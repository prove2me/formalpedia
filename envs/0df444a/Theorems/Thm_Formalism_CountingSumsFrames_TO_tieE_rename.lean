-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_tieE_rename
-- name    : Formalism.CountingSumsFrames.TO.tieE_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:55.770391+00:00
-- url     : https://prove2.me/theorems/9bc01102-46f0-4f5b-a849-864e604a1e2f
-- title:
--   TO: tie E rename
-- statement:
--   The TO construction uses the tie E rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1441-L1443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1441-L1443

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

theorem Formalism.CountingSumsFrames.TO.tieE_rename {τ : Type} {r : ℕ} (ι : σ → τ) (w e : Fin r → σ) (F : MvPolynomial σ k) :
    Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieE w e F) := by sorry
