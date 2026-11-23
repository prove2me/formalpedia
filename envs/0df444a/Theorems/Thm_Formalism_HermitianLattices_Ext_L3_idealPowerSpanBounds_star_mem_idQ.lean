-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mem_idQ
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.star_mem_idQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:48.230689+00:00
-- url     : https://prove2.me/theorems/954bd4d4-ab9a-4f29-a514-9272cab1905c
-- title:
--   ideal Power Span Bounds: star mem id Q
-- statement:
--   The ideal Power Span Bounds construction uses the star mem id Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean#L128-L132

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
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

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.star_mem_idQ [hF : Fact (IsFixF K F)] {𝔭 : Ideal (𝓞 F)} {k j : ℕ}
    {a : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) : star a ∈ idQ K 𝔭 k j := by sorry
