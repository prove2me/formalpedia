-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_alpha
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exists_alpha
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:57.628079+00:00
-- url     : https://prove2.me/theorems/417991da-3a7f-4cfe-a250-348ad274a703
-- title:
--   Cell: exists alpha
-- statement:
--   The Cell construction uses the exists alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L127-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L127-L181

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

theorem Formalism.HermitianLattices.Ext.L3.Cell.exists_alpha (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ∈ 𝔭) (ha2 : a ∉ 𝔭 ^ 2) (ha' : a' ∈ 𝔭) (ha'2 : a' ∉ 𝔭 ^ 2) :
    ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ a * ν + a' ∈ 𝔭 ^ 2 ∧ a * ν + a' ∉ 𝔭 ^ 3 := by sorry
