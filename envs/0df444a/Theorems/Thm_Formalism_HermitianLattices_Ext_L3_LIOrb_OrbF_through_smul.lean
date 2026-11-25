-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_through_smul
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.through_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:16.888819+00:00
-- url     : https://prove2.me/theorems/0d3b1a31-5aca-5fed-9128-f36a23aed836
-- title:
--   Orb F: through smul
-- statement:
--   The Orb F construction uses the through smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AutSubApplyMem.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AutSubApplyMem.lean#L40-L48

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AutSubApplyMem
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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.through_smul (hs : h.IsSymm) (S : VecSplit h h') {A M : Submodule (𝓞 K) V}
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (hM : (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = M) ∧ S.x₀ ∈ M) :
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M) ∧
      S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M := by sorry
