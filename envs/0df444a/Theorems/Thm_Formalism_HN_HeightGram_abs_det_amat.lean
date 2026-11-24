-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_abs_det_amat
-- name    : Formalism.HN.HeightGram.abs_det_amat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:56.402875+00:00
-- url     : https://prove2.me/theorems/bcb4fb69-27d3-4cca-b342-790b7e8bc24e
-- title:
--   Height Gram: abs det amat
-- statement:
--   The Height Gram construction uses the abs det amat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L218-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L218-L243

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
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
attribute [local instance] isEmpty_real
open scoped Classical
open MeasureTheory ZSpan

theorem Formalism.HN.HeightGram.abs_det_amat (eS : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ InfinitePlace K × Fin 2) :
    |(amat (lamK K) eS).det| = (2⁻¹) ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| := by sorry
