-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unit_factor
-- name    : Formalism.HermitianLattices.Ext.L3.D2.exists_unit_factor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:16.622405+00:00
-- url     : https://prove2.me/theorems/041113ed-e836-4da6-8002-d2e7eeda8e7e
-- title:
--   D2: exists unit factor
-- statement:
--   The D2 construction uses the exists unit factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L109-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L109-L138

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
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

theorem Formalism.HermitianLattices.Ext.L3.D2.exists_unit_factor {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) {D : 𝓞 F} (hD0 : D ≠ 0) :
    ∃ w : K, w ∈ pK K 𝔭 0 ∧ w⁻¹ ∈ pK K 𝔭 0 ∧ w ≠ 0 ∧
      algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D * w := by sorry
