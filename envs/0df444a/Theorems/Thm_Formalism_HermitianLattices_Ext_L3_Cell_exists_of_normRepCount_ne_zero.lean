-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_of_normRepCount_ne_zero
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exists_of_normRepCount_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:33:11.901066+00:00
-- url     : https://prove2.me/theorems/0468d642-37c5-4f3c-a011-a7ffdd091395
-- title:
--   Cell: exists of norm Rep Count ne zero
-- statement:
--   The Cell construction uses the exists of norm Rep Count ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L20-L26

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}

theorem Formalism.HermitianLattices.Ext.L3.Cell.exists_of_normRepCount_ne_zero {Q : Ideal (𝓞 K)} {n : 𝓞 K} (h : normRepCount K Q 1 n ≠ 0) :
    ∃ α : 𝓞 K, conjO K α * α - n ∈ Q := by sorry
