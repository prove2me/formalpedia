-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_basis_mem_locF
-- name    : Formalism.HermitianLattices.Ext.L3.D2.basis_mem_locF
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:03.500823+00:00
-- url     : https://prove2.me/theorems/fc524631-c3cf-40a2-84d2-e64badede1d8
-- title:
--   D2: basis mem loc F
-- statement:
--   The D2 construction uses the basis mem loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L142-L144

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

theorem Formalism.HermitianLattices.Ext.L3.D2.basis_mem_locF {κ : Type} (a : Basis κ K V) (𝔭 : Ideal (𝓞 F)) (i : κ) :
    a i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) := by sorry
