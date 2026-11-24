-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_pair
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exists_pair
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:44:03.614901+00:00
-- url     : https://prove2.me/theorems/678577be-4f34-4773-a2f8-ed242b453808
-- title:
--   Cell: exists pair
-- statement:
--   The Cell construction uses the exists pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormalise.lean#L46-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormalise.lean#L46-L83

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

theorem Formalism.HermitianLattices.Ext.L3.Cell.exists_pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
    (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
    (hap : a ∈ 𝔭) :
    ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
      h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by sorry
