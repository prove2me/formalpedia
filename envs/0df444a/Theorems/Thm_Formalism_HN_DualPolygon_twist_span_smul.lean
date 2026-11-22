-- Prove2me | Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul
-- name    : Formalism.HN.DualPolygon.twist_span_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:15.759807+00:00
-- url     : https://prove2.me/theorems/0a87fa73-4035-4a06-8d00-f62e24984955
-- title:
--   Dual Polygon: twist span smul
-- statement:
--   The Dual Polygon construction uses the twist span smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L514-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L514-L528

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
attribute [local instance] Ideal.Quotient.field
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]

theorem Formalism.HN.DualPolygon.twist_span_smul (X : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)) (h : 𝔞 ≠ ⊥) :
    Submodule.span K ((𝔞 • X : Submodule (𝓞 K) W) : Set W) = Submodule.span K (X : Set W) := by sorry
