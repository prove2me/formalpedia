-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale_fixed
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exists_scale_fixed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:10.39892+00:00
-- url     : https://prove2.me/theorems/9de752d9-e979-49e7-9b14-2ead51d68ce8
-- title:
--   Cell: exists scale fixed
-- statement:
--   The Cell construction uses the exists scale fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L108-L125

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

theorem Formalism.HermitianLattices.Ext.L3.Cell.exists_scale_fixed (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {d : K} (hd0 : d ≠ 0)
    (hds : star d = d) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * d = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by sorry
