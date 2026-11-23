-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_two_le_absNorm
-- name    : Formalism.HermitianLattices.Ext.L3.vectorCountBounds.two_le_absNorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:10.563528+00:00
-- url     : https://prove2.me/theorems/a3ca6076-3d47-4fda-80ef-139215c5fbf5
-- title:
--   vector Count Bounds: two le abs Norm
-- statement:
--   The vector Count Bounds construction uses the two le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L39-L46

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.vectorCountBounds.two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 := by sorry
