-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_eq_zero_of_inQ_one
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.eq_zero_of_inQ_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:36.021904+00:00
-- url     : https://prove2.me/theorems/4ba6070c-0cc9-4e9a-bf77-833a2b6f8a44
-- title:
--   unitary Absolute Value Bounds: eq zero of in Q one
-- statement:
--   The unitary Absolute Value Bounds construction uses the eq zero of in Q one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L158-L161

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

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.eq_zero_of_inQ_one {𝔭 : Ideal (𝓞 F)} {a : AQ K 𝔭 1} (ha : InQ 𝔭 1 a) : a = 0 := by sorry
