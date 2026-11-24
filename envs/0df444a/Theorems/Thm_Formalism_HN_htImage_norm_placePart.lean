-- Prove2me | Theorems.Thm_Formalism_HN_htImage_norm_placePart
-- name    : Formalism.HN.htImage_norm_placePart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:24.428552+00:00
-- url     : https://prove2.me/theorems/52601ee2-dec7-4594-9364-4875ad1450ff
-- title:
--   HN: ht Image norm place Part
-- statement:
--   The HN construction uses the ht Image norm place Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L195-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L195-L214

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

theorem Formalism.HN.htImage_norm_placePart {P ι : Type*} [Fintype P] [Fintype ι] {v : P}
    {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    ‖y‖ = ‖(WithLp.toLp 2 (htImageCv y v) : EuclideanSpace ℂ ι)‖ := by sorry
