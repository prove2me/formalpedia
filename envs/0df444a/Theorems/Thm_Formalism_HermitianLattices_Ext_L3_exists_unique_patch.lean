-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_unique_patch
-- name    : Formalism.HermitianLattices.Ext.L3.exists_unique_patch
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:29.748976+00:00
-- url     : https://prove2.me/theorems/3f7db1b5-42f5-4219-a66b-7872a903fe02
-- title:
--   L3: exists unique patch
-- statement:
--   The L3 construction uses the exists unique patch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtIffVd.lean#L151-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtIffVd.lean#L151-L182

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.exists_unique_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (T : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hT : ∀ 𝔭 ∈ s, locF 𝔭.1 (T 𝔭) = T 𝔭 ∧ ∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧
      locF 𝔭.1 A = T 𝔭) :
    ∃! Λ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ ∧ (∀ 𝔭 ∈ s, locF 𝔭.1 Λ = T 𝔭) ∧
      ∀ 𝔭 ∉ s, locF 𝔭.1 Λ = locF 𝔭.1 L₀ := by sorry
