-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_span_pow_mul_le
-- name    : Formalism.HermitianLattices.Ext.L3.HU.span_pow_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:07.247124+00:00
-- url     : https://prove2.me/theorems/8632e631-a72a-4df4-a143-c65af7e849dd
-- title:
--   HU: span pow mul le
-- statement:
--   The HU construction uses the span pow mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L151-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L151-L159

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

theorem Formalism.HermitianLattices.Ext.L3.HU.span_pow_mul_le {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F}
    (h : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}) (k : ℕ) :
    Ideal.span {ι (s₀ ^ k)} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π₀ ^ k)} := by sorry
