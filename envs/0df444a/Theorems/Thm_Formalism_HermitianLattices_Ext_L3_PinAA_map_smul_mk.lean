-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_map_smul_mk
-- name    : Formalism.HermitianLattices.Ext.L3.PinAA.map_smul_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:17.152891+00:00
-- url     : https://prove2.me/theorems/ee7dc73f-cbe5-4f5d-92d3-e2a2608d279b
-- title:
--   Pin AA: map smul mk
-- statement:
--   The Pin AA construction uses the map smul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulEqZeroIff.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulEqZeroIff.lean#L108-L114

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.PinAA.map_smul_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (c : 𝓞 F) (H : Matrix κ κ (𝓞 K)) :
    (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) • H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by sorry
