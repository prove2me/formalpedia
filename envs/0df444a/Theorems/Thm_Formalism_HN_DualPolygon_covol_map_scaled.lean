-- Prove2me | Theorems.Thm_Formalism_HN_DualPolygon_covol_map_scaled
-- name    : Formalism.HN.DualPolygon.covol_map_scaled
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:07.500205+00:00
-- url     : https://prove2.me/theorems/1e36b959-a177-419f-a88e-457c529311e5
-- title:
--   Dual Polygon: covol map scaled
-- statement:
--   The Dual Polygon construction uses the covol map scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L360-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L360-L412

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.HN.DualPolygon.covol_map_scaled (φ : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hφ : ∀ x y, inner ℝ (φ x) (φ y) = c ^ 2 * inner ℝ x y) (M : Submodule ℤ E)
    [DiscreteTopology M] :
    DiscreteTopology (M.map (φ.restrictScalars ℤ)) ∧
      Formalism.F.rk (M.map (φ.restrictScalars ℤ)) = Formalism.F.rk M ∧
      Formalism.F.covol (M.map (φ.restrictScalars ℤ)) = c ^ Formalism.F.rk M * Formalism.F.covol M := by sorry
