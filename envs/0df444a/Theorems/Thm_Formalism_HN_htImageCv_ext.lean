-- Prove2me | Theorems.Thm_Formalism_HN_htImageCv_ext
-- name    : Formalism.HN.htImageCv_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:47.565055+00:00
-- url     : https://prove2.me/theorems/b7c8439d-d99d-4eb9-b970-6a5aad679e11
-- title:
--   HN: ht Image Cv ext
-- statement:
--   The HN construction uses the ht Image Cv ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L164-L171

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

theorem Formalism.HN.htImageCv_ext {P ι : Type*} [Fintype P] [Fintype ι] {y z : EuclideanSpace ℝ (P × ι × Fin 2)}
    (h : ∀ v, htImageCv y v = htImageCv z v) : y = z := by sorry
