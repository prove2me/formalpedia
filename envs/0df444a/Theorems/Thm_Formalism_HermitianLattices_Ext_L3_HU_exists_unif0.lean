-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_unif0
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_unif0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:36.063017+00:00
-- url     : https://prove2.me/theorems/31c8afc7-35b1-49ef-b243-befa9559ded8
-- title:
--   HU: exists unif0
-- statement:
--   The HU construction uses the exists unif0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L127-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L127-L149

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

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_unif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ π₀ ∈ 𝔭, π₀ ∉ 𝔭 ^ 2 ∧ ∃ s₀ : 𝓞 F, s₀ ∉ 𝔭 ∧ Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀} := by sorry
