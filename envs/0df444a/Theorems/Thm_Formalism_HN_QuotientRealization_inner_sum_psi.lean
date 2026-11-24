-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_inner_sum_psi
-- name    : Formalism.HN.QuotientRealization.inner_sum_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:19.939285+00:00
-- url     : https://prove2.me/theorems/c141103f-87ff-47c8-873f-a9aa995082a2
-- title:
--   Quotient Realization: inner sum psi
-- statement:
--   The Quotient Realization construction uses the inner sum psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L119-L122

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

theorem Formalism.HN.QuotientRealization.inner_sum_psi (y z : P → ι → ℂ) :
    inner ℝ (∑ u, PlaceDecomposition.psi u (y u)) (∑ v, PlaceDecomposition.psi (ι := ι) v (z v)) =
      ∑ v, (inner ℂ (WithLp.toLp 2 (y v) : EuclideanSpace ℂ ι) (WithLp.toLp 2 (z v))).re := by sorry
