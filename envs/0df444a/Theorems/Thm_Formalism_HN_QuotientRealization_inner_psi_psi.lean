-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_inner_psi_psi
-- name    : Formalism.HN.QuotientRealization.inner_psi_psi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:02.210851+00:00
-- url     : https://prove2.me/theorems/1cf19023-0716-4624-b94e-9fba701e156d
-- title:
--   Quotient Realization: inner psi psi
-- statement:
--   The Quotient Realization construction uses the inner psi psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L94-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L94-L117

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
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
open Formalism.HN.QuotientRealization
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]

theorem Formalism.HN.QuotientRealization.inner_psi_psi (u v : P) (y z : ι → ℂ) :
    inner ℝ (PlaceDecomposition.psi u y) (PlaceDecomposition.psi (ι := ι) v z) =
      if u = v then (inner ℂ (WithLp.toLp 2 y : EuclideanSpace ℂ ι) (WithLp.toLp 2 z)).re
      else 0 := by sorry
