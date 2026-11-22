-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_trF_spec
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.trF_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:43.514795+00:00
-- url     : https://prove2.me/theorems/0dcfe19d-b967-4adc-865d-96b713f336da
-- title:
--   ideal Power Span Bounds: tr F spec
-- statement:
--   The ideal Power Span Bounds construction uses the tr F spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L256-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L256-L256

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

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.trF_spec (hF : IsFixF K F) (z : 𝓞 K) : ι (trF hF z) = z + conjO K z := by sorry
