-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_trF_mem_pow
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.trF_mem_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:56.782185+00:00
-- url     : https://prove2.me/theorems/003499e2-e9c5-4fbb-b5fa-c001d1dd961c
-- title:
--   ideal Power Span Bounds: tr F mem pow
-- statement:
--   The ideal Power Span Bounds construction uses the tr F mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L258-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L258-L261

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.trF_mem_pow (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    trF hF z ∈ 𝔭 ^ k := by sorry
