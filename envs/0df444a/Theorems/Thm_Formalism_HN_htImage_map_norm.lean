-- Prove2me | Theorems.Thm_Formalism_HN_htImage_map_norm
-- name    : Formalism.HN.htImage_map_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:00.046413+00:00
-- url     : https://prove2.me/theorems/f55edfd6-fa02-453a-8f60-1c8248a92b4c
-- title:
--   HN: ht Image map norm
-- statement:
--   The HN construction uses the ht Image map norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L216-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L216-L223

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
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
open Formalism Formalism.HN

theorem Formalism.HN.htImage_map_norm {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : P → Matrix κ ι ℂ) {v : P} {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    ‖htImageMap M y‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M v))‖ * ‖y‖ := by sorry
