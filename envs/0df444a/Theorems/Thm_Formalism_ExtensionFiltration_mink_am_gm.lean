-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_mink_am_gm
-- name    : Formalism.ExtensionFiltration.mink_am_gm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:28.731809+00:00
-- url     : https://prove2.me/theorems/cfe2e5b9-7b9a-4873-8e3a-e03c74332763
-- title:
--   Extension Filtration: mink am gm
-- statement:
--   The Extension Filtration construction uses the mink am gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/MuMaxMinkowski.lean#L64-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/MuMaxMinkowski.lean#L64-L90

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.ExtensionFiltration.mink_am_gm {σ : Type} [Fintype σ] [Nonempty σ] (a : σ → ℝ) (ha : ∀ v, 0 < a v) :
    (Fintype.card σ : ℝ) * Real.exp (2 * ((1 / (Fintype.card σ : ℝ)) * ∑ v, Real.log (a v))) ≤
      ∑ v, a v ^ 2 := by sorry
