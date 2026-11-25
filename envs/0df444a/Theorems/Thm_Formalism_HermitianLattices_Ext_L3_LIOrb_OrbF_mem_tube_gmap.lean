-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_mem_tube_gmap
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.mem_tube_gmap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:27:35.756901+00:00
-- url     : https://prove2.me/theorems/556a0506-cfa6-50e0-9355-9bd2229ba6d5
-- title:
--   Orb F: mem tube gmap
-- statement:
--   The Orb F construction uses the mem tube gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean#L113-L127

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsGlobalOfFibLocNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.mem_tube_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x y : V) :
    g y ∈ tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x ↔
      y ∈ tube (autSub h A) A 𝔭 J (g.symm x) := by sorry
