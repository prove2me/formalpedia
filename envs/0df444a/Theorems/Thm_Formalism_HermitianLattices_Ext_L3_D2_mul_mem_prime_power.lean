-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_prime_power
-- name    : Formalism.HermitianLattices.Ext.L3.D2.mul_mem_prime_power
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:14.834179+00:00
-- url     : https://prove2.me/theorems/ee40b5cc-29d3-4912-b81f-93f377b9384c
-- title:
--   D2: mul mem prime power
-- statement:
--   The D2 construction uses the mul mem prime power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L140-L143

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

theorem Formalism.HermitianLattices.Ext.L3.D2.mul_mem_prime_power {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a b : K} (ha : a ∈ pK K 𝔭 0)
    (hb : b ∈ pK K 𝔭 0) : a * b ∈ pK K 𝔭 0 := by sorry
