-- Prove2me | Theorems.Thm_Formalism_HN_htImageCv_map
-- name    : Formalism.HN.htImageCv_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:15.270223+00:00
-- url     : https://prove2.me/theorems/8534e3f7-727d-4402-8db6-5217bc549584
-- title:
--   HN: ht Image Cv map
-- statement:
--   The HN construction uses the ht Image Cv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L173-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L173-L177

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

theorem Formalism.HN.htImageCv_map {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] (M : P → Matrix κ ι ℂ)
    (y : EuclideanSpace ℝ (P × ι × Fin 2)) (v : P) :
    htImageCv (htImageMap M y) v = (M v).mulVec (htImageCv y v) := by sorry
