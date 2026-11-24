-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsUnif0_ne_zero
-- name    : Formalism.HermitianLattices.Ext.L3.HU.IsUnif0.ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:06.619275+00:00
-- url     : https://prove2.me/theorems/25bf00b6-0133-49c7-b745-f6fd1303f639
-- title:
--   Is Unif0: ne zero
-- statement:
--   The Is Unif0 construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeZeroOfNotMem.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeZeroOfNotMem.lean#L35-L37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem Formalism.HermitianLattices.Ext.L3.HU.IsUnif0.ne_zero {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) : π₀ ≠ 0 := by sorry
