-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_finrank_biSup_le
-- name    : Formalism.CountingSumsFrames.TO.finrank_biSup_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:38.298629+00:00
-- url     : https://prove2.me/theorems/adb7a8ed-1eaa-46ba-91a6-3f1239faab22
-- title:
--   TO: finrank bi Sup le
-- statement:
--   The TO construction uses the finrank bi Sup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2687-L2700
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2687-L2700

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

theorem Formalism.CountingSumsFrames.TO.finrank_biSup_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (Yv : Submodule K V)
    [FiniteDimensional K Yv] (A : ι → Submodule K V) (hA : ∀ i, A i ≤ Yv) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, A i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (A i) := by sorry
