-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
-- name    : Formalism.HermitianLattices.Ext.L3.HU.InP.mem_SP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:23.709098+00:00
-- url     : https://prove2.me/theorems/468d54d9-a225-49e3-a957-b6f805638fa0
-- title:
--   In P: mem SP
-- statement:
--   The In P construction uses the mem SP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean#L109-L109

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

theorem Formalism.HermitianLattices.Ext.L3.HU.InP.mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a : K} (ha : InP 𝔭 k a) : a ∈ SP K 𝔭 := by sorry
