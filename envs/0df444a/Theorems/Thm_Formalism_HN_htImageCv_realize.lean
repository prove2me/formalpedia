-- Prove2me | Theorems.Thm_Formalism_HN_htImageCv_realize
-- name    : Formalism.HN.htImageCv_realize
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:16.697721+00:00
-- url     : https://prove2.me/theorems/4591b339-29ff-41fd-9bf8-ff081c9f7f35
-- title:
--   HN: ht Image Cv realize
-- statement:
--   The HN construction uses the ht Image Cv realize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L229-L233

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
variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type*} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem Formalism.HN.htImageCv_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) :
    htImageCv (Formalism.HermitianLatticesTheory.realize b X x) v = Formalism.HermitianLatticesTheory.fcoord b X v x := by sorry
