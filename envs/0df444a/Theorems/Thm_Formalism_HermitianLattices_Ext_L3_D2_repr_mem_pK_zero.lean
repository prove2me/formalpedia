-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_repr_mem_pK_zero
-- name    : Formalism.HermitianLattices.Ext.L3.D2.repr_mem_pK_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:10.417088+00:00
-- url     : https://prove2.me/theorems/b196c728-eff7-4ea5-913d-e5bfe0486a75
-- title:
--   D2: repr mem p K zero
-- statement:
--   The D2 construction uses the repr mem p K zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L146-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L146-L153

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
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

theorem Formalism.HermitianLattices.Ext.L3.D2.repr_mem_pK_zero {κ : Type} (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {x : V} (hx : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) (i : κ) :
    a.repr x i ∈ pK K 𝔭 0 := by sorry
