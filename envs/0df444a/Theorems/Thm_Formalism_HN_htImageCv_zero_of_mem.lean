-- Prove2me | Theorems.Thm_Formalism_HN_htImageCv_zero_of_mem
-- name    : Formalism.HN.htImageCv_zero_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:17.309843+00:00
-- url     : https://prove2.me/theorems/b814cec2-934c-47cc-a229-e48decfd7721
-- title:
--   HN: ht Image Cv zero of mem
-- statement:
--   The HN construction uses the ht Image Cv zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L179-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L179-L185

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

theorem Formalism.HN.htImageCv_zero_of_mem {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (h : w ≠ v)
    {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) : htImageCv y w = 0 := by sorry
