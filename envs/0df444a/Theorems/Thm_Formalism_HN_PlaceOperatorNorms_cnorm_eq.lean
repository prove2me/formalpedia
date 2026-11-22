-- Prove2me | Theorems.Thm_Formalism_HN_PlaceOperatorNorms_cnorm_eq
-- name    : Formalism.HN.PlaceOperatorNorms.cnorm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:28.984852+00:00
-- url     : https://prove2.me/theorems/d87d9994-3fcd-47b4-8272-875f701eed21
-- title:
--   Place Operator Norms: cnorm eq
-- statement:
--   The Place Operator Norms construction uses the cnorm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneqMean.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneqMean.lean#L45-L46

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
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
open Formalism.HN.PlaceOperatorNorms
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem Formalism.HN.PlaceOperatorNorms.cnorm_eq (u : κ → ℂ) : Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ := by sorry
