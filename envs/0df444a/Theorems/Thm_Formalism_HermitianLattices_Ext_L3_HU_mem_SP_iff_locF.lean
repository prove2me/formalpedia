-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP_iff_locF
-- name    : Formalism.HermitianLattices.Ext.L3.HU.mem_SP_iff_locF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:26.667593+00:00
-- url     : https://prove2.me/theorems/6ff35d02-61da-4bdc-acf4-4d7fbc5c87b1
-- title:
--   HU: mem SP iff loc F
-- statement:
--   The HU construction uses the mem SP iff loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L79-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L79-L104

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
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

theorem Formalism.HermitianLattices.Ext.L3.HU.mem_SP_iff_locF {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ a ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by sorry
