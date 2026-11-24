-- Prove2me | Theorems.Thm_Formalism_HN_htImage_map_realize
-- name    : Formalism.HN.htImage_map_realize
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:20.993556+00:00
-- url     : https://prove2.me/theorems/40c01a8f-a6d1-4f37-b3b0-43b4a66f3e33
-- title:
--   HN: ht Image map realize
-- statement:
--   The HN construction uses the ht Image map realize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L256-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L256-L271

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

theorem Formalism.HN.htImage_map_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] W) (x : V) :
    htImageMap (htImageMat b X b' X' φ) (Formalism.HermitianLatticesTheory.realize b X x) =
      Formalism.HermitianLatticesTheory.realize b' X' (φ x) := by sorry
