-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_star
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.piQ_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:11.426291+00:00
-- url     : https://prove2.me/theorems/db483ad7-2e2e-4822-adf0-1010c0d14666
-- title:
--   ideal Power Span Bounds: pi Q star
-- statement:
--   The ideal Power Span Bounds construction uses the pi Q star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean#L72-L75

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

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.piQ_star [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    piQ K 𝔭 k (star a) = star (piQ K 𝔭 k a) := by sorry
