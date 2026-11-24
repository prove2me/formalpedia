-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_majAt_smul
-- name    : Formalism.HN.HeightGram.majAt_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:51.315893+00:00
-- url     : https://prove2.me/theorems/06a7b6d4-ac6e-42da-a3f8-5cd512a08a9f
-- title:
--   Height Gram: maj At smul
-- statement:
--   The Height Gram construction uses the maj At smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L71-L77

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.HeightGram.majAt_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a a' : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) (a' • y) =
      star (v.embedding a) * v.embedding a' * Formalism.HermitianLatticesTheory.majAt b X v x y := by sorry
