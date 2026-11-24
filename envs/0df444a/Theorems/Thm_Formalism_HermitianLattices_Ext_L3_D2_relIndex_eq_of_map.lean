-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_relIndex_eq_of_map
-- name    : Formalism.HermitianLattices.Ext.L3.D2.relIndex_eq_of_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:20.63987+00:00
-- url     : https://prove2.me/theorems/b7767310-2f52-45ed-841e-b9e020805e9d
-- title:
--   D2: rel Index eq of map
-- statement:
--   The D2 construction uses the rel Index eq of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfMap.lean#L14-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfMap.lean#L14-L45

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfMap
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

theorem Formalism.HermitianLattices.Ext.L3.D2.relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H G' : Subgroup G)
    (N P : AddSubgroup M) (φ : G → M) (h1 : ∀ x ∈ G', φ x ∈ P) (h2 : ∀ p ∈ P, ∃ x ∈ G', φ x = p)
    (h3 : ∀ x ∈ G', ∀ y ∈ G', x⁻¹ * y ∈ H ↔ φ y - φ x ∈ N) : H.relIndex G' = N.relIndex P := by sorry
