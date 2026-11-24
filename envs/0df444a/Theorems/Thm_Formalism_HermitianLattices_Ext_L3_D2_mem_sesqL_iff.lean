-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_sesqL_iff
-- name    : Formalism.HermitianLattices.Ext.L3.D2.mem_sesqL_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:46:57.056796+00:00
-- url     : https://prove2.me/theorems/83d3d8c6-d4d8-49bc-a955-14e0f44f9e36
-- title:
--   D2: mem sesq L iff
-- statement:
--   The D2 construction uses the mem sesq L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L197-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L197-L213

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

theorem Formalism.HermitianLattices.Ext.L3.D2.mem_sesqL_iff (hF : IsFixF K F) {κ : Type} [Fintype κ] (a : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (s : V →ₗ⋆[K] V →ₗ[K] K) :
    s ∈ sesqL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) 𝔭 k ↔
      ∀ i j, s (a i) (a j) ∈ pK K 𝔭 k := by sorry
