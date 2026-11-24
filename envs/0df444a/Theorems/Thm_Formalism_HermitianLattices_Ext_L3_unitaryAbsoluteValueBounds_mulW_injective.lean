-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mulW_injective
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.mulW_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:27.847345+00:00
-- url     : https://prove2.me/theorems/61f061e8-0534-4786-93fe-7751250e3b18
-- title:
--   unitary Absolute Value Bounds: mul W injective
-- statement:
--   The unitary Absolute Value Bounds construction uses the mul W injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L28-L35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.mulW_injective {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) : Function.Injective (mulW (K := K) 𝔭 (map_mem h1) j) := by sorry
