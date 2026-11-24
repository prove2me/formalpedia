-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_normalise
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exists_normalise
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:30.834862+00:00
-- url     : https://prove2.me/theorems/3e738da1-8b0b-491b-be1d-209162b16dac
-- title:
--   Cell: exists normalise
-- statement:
--   The Cell construction uses the exists normalise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormalise.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormalise.lean#L33-L44

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
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
variable {V : Type} [AddCommGroup V] [Module K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}

theorem Formalism.HermitianLattices.Ext.L3.Cell.exists_normalise (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
    ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by sorry
