-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mk_mem_ker_piQ
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mk_mem_ker_piQ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:15.086236+00:00
-- url     : https://prove2.me/theorems/a2820df5-ecb8-4ca8-b1fa-ab79c7580db5
-- title:
--   ideal Power Span Bounds: mk mem ker pi Q
-- statement:
--   The ideal Power Span Bounds construction uses the mk mem ker pi Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean#L77-L79

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

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mk_mem_ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) a ∈ RingHom.ker (piQ K 𝔭 k) ↔ a ∈ extP K 𝔭 ^ k := by sorry
