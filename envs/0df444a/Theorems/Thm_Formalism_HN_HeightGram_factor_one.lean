-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_factor_one
-- name    : Formalism.HN.HeightGram.factor_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:07.986878+00:00
-- url     : https://prove2.me/theorems/a3cb68ec-5af9-4ecf-a8db-ee829c84d5da
-- title:
--   Height Gram: factor one
-- statement:
--   The Height Gram construction uses the factor one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L305-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L305-L317

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

theorem Formalism.HN.HeightGram.factor_one (f j : ℕ) {D : ℝ} (hD : 0 < D) :
    (2 : ℝ) ^ (f * j) * D ^ (-(j : ℝ) / 2) * (((2 : ℝ)⁻¹) ^ f * √D) ^ j = 1 := by sorry
