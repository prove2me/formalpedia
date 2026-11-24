-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_mmwZ_mmw
-- name    : Formalism.CountingSumsFrames.TO.mmwZ_mmw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:11.230251+00:00
-- url     : https://prove2.me/theorems/14496eba-6d9f-4236-a5d5-45afa61594e1
-- title:
--   TO: mmw Z mmw
-- statement:
--   The TO construction uses the mmw Z mmw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3288-L3290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3288-L3290

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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.mmwZ_mmw [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ MMw p LLw J M ρ w := by sorry
