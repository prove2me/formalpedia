-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_mem_smul
-- name    : Formalism.HermitianLattices.Ext.L3.D2.smul_mem_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:28:59.430009+00:00
-- url     : https://prove2.me/theorems/f25f8da3-dcc3-4709-9cc2-94c311dbf508
-- title:
--   D2: smul mem smul
-- statement:
--   The D2 construction uses the smul mem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulDvdUnif.lean#L193-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulDvdUnif.lean#L193-L201

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

theorem Formalism.HermitianLattices.Ext.L3.D2.smul_mem_smul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V) {i j : ℕ}
    {a : K} {x : V} (ha : a ∈ pK K 𝔭 i) (hx : x ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    a • x ∈ extP K 𝔭 ^ (i + j) • locF 𝔭 A₀ := by sorry
