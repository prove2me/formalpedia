-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
-- name    : Formalism.HermitianLattices.Ext.L3.D2.mem_smul_iff_unif
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:28:45.762206+00:00
-- url     : https://prove2.me/theorems/bdb64094-0633-40d6-9c38-895152c449cc
-- title:
--   D2: mem smul iff unif
-- statement:
--   The D2 construction uses the mem smul iff unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulDvdUnif.lean#L155-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulDvdUnif.lean#L155-L176

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.D2.mem_smul_iff_unif {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (A₀ : Submodule (𝓞 K) V) {k : ℕ} {x : V} :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ ↔ ∃ y ∈ locF 𝔭 A₀, x = algebraMap F K (π : F) ^ k • y := by sorry
