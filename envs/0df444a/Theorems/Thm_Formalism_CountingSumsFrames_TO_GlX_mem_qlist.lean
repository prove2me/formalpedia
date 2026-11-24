-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_mem_qlist
-- name    : Formalism.CountingSumsFrames.TO.GlX.mem_qlist
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:59.992951+00:00
-- url     : https://prove2.me/theorems/bc274798-987e-45b1-ac27-d4dcbb336481
-- title:
--   Gl X: mem qlist
-- statement:
--   The Gl X construction uses the mem qlist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L62-L66

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

theorem Formalism.CountingSumsFrames.TO.GlX.mem_qlist {S : Finset (Fin r → ℤ)} {c : ℤ} {ν : Fin r → ℤ} (hν : ν ∈ S) (hne : GlW.casI ν ≠ c) :
    GlW.casI ν ∈ qlist S c := by sorry
