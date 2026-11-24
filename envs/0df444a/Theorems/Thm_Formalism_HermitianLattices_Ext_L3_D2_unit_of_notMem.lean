-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unit_of_notMem
-- name    : Formalism.HermitianLattices.Ext.L3.D2.unit_of_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:48.099817+00:00
-- url     : https://prove2.me/theorems/6efbcd2d-ecaf-4217-89f5-7f904400eb37
-- title:
--   D2: unit of not Mem
-- statement:
--   The D2 construction uses the unit of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L100-L107

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

theorem Formalism.HermitianLattices.Ext.L3.D2.unit_of_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : 𝓞 F} (hs𝔭 : s ∉ 𝔭) :
    algebraMap (𝓞 K) K (ι s) ∈ pK K 𝔭 0 ∧ (algebraMap (𝓞 K) K (ι s))⁻¹ ∈ pK K 𝔭 0 ∧
      algebraMap (𝓞 K) K (ι s) ≠ 0 := by sorry
