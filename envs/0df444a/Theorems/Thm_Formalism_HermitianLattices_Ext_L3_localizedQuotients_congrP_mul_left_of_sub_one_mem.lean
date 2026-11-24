-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_congrP_mul_left_of_sub_one_mem
-- name    : Formalism.HermitianLattices.Ext.L3.localizedQuotients.congrP_mul_left_of_sub_one_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:00.530529+00:00
-- url     : https://prove2.me/theorems/5d2b0c8e-503c-43b3-96f5-844483a60254
-- title:
--   localized Quotients: congr P mul left of sub one mem
-- statement:
--   The localized Quotients construction uses the congr P mul left of sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L108-L117

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.localizedQuotients.congrP_mul_left_of_sub_one_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} {c : 𝓞 F} (hc : c - 1 ∈ 𝔭 ^ k) {a : K} {n : 𝓞 F}
    (h : CongrP 𝔭 k a (algebraMap F K (n : F))) :
    CongrP 𝔭 k (algebraMap (𝓞 K) K (ι c) * a) (algebraMap F K (n : F)) := by sorry
