-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_iSup_stable
-- name    : Formalism.CountingSumsFrames.TO.GlX.iSup_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:49.788622+00:00
-- url     : https://prove2.me/theorems/58c3c9c3-540f-4cda-9a02-c6c6392c5bdb
-- title:
--   Gl X: i Sup stable
-- statement:
--   The Gl X construction uses the i Sup stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L118-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L118-L127

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
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.TO.GlX.iSup_stable {ι : Sort*} {U : ι → Submodule K V} (hU : ∀ i, G.Stable (U i)) : G.Stable (⨆ i, U i) := by sorry
