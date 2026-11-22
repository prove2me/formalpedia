-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_norm_det_gramPl
-- name    : Formalism.HN.HeightGram.norm_det_gramPl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:40.153481+00:00
-- url     : https://prove2.me/theorems/6d371a62-8bcb-44d1-8326-1a1eb15aa6a5
-- title:
--   Height Gram: norm det gram Pl
-- statement:
--   The Height Gram construction uses the norm det gram Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L320-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L320-L336

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
open scoped ComplexOrder

theorem Formalism.HN.HeightGram.norm_det_gramPl {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) :
    ‖(gramPl b X v e).det‖ = (gramPl b X v e).det.re := by sorry
