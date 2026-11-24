-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_inQ_iff_range
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.inQ_iff_range
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:54:34.996244+00:00
-- url     : https://prove2.me/theorems/ef6a2284-7da0-43be-9686-d51cec6ed919
-- title:
--   unitary Absolute Value Bounds: in Q iff range
-- statement:
--   The unitary Absolute Value Bounds construction uses the in Q iff range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L37-L51

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

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.inQ_iff_range {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) (a : AQ K 𝔭 (j + 2)) : InQ 𝔭 (j + 2) a ↔ ∃ b, mulW (K := K) 𝔭 (map_mem h1) j b = a := by sorry
