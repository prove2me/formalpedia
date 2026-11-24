-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_mem_smul_of_smul_mem
-- name    : Formalism.HermitianLattices.Ext.L3.D2.RedC.mem_smul_of_smul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:01.473889+00:00
-- url     : https://prove2.me/theorems/bd4fdcb4-f88e-4305-9a68-15a4335c45b9
-- title:
--   Red C: mem smul of smul mem
-- statement:
--   The Red C construction uses the mem smul of smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean#L86-L94

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
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
open Formalism.HermitianLattices.Ext.L3.D2.RedC

theorem Formalism.HermitianLattices.Ext.L3.D2.RedC.mem_smul_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A : Submodule (𝓞 K) V) (k : ℕ)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (hv : v ∈ A)
    (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ extP K 𝔭 ^ k • A) : v ∈ extP K 𝔭 ^ k • A := by sorry
