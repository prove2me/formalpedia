-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nSub_le_sSub
-- name    : Formalism.HermitianLattices.Ext.L3.D2.nSub_le_sSub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:43.041767+00:00
-- url     : https://prove2.me/theorems/51484bcd-fbea-45e8-8da1-287e30992376
-- title:
--   D2: n Sub le s Sub
-- statement:
--   The D2 construction uses the n Sub le s Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsDualBound.lean#L85-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsDualBound.lean#L85-L98

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.D2.nSub_le_sSub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    nSub (locF 𝔭 A₀) 𝔭 k ≤ sSub h (locF 𝔭 A₀) 𝔭 k := by sorry
