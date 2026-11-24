-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exists_scale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:32:47.016443+00:00
-- url     : https://prove2.me/theorems/bf511c4a-9a24-4e38-a14e-d188cb45cfa3
-- title:
--   Cell: exists scale
-- statement:
--   The Cell construction uses the exists scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L63-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOfNormRepCountNeZero.lean#L63-L97

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

theorem Formalism.HermitianLattices.Ext.L3.Cell.exists_scale (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} {r k : ℕ}
    (h1 : a₁ ∈ 𝔭 ^ (r + r + k)) (h2 : a₁ ∉ 𝔭 ^ (r + r + k + 1)) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ (k + 1) := by sorry
