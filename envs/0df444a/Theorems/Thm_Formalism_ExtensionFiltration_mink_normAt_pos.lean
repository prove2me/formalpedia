-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_mink_normAt_pos
-- name    : Formalism.ExtensionFiltration.mink_normAt_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:28.293564+00:00
-- url     : https://prove2.me/theorems/00a50f6e-f07e-4d80-8f82-f13f95e0d1dc
-- title:
--   Extension Filtration: mink norm At pos
-- statement:
--   The Extension Filtration construction uses the mink norm At pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/MuMaxMinkowski.lean#L38-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/MuMaxMinkowski.lean#L38-L62

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

theorem Formalism.ExtensionFiltration.mink_normAt_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (x : V) (hx : x ≠ 0) :
    0 < Formalism.HermitianLatticesTheory.normAt b X v x := by sorry
