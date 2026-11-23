-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_patch
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.patch
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:58.486432+00:00
-- url     : https://prove2.me/theorems/83c3879d-6fda-4ea6-bc19-e1a6a1b9855a
-- title:
--   Loc F: patch
-- statement:
--   The Loc F construction uses the patch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L120-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L120-L204

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LocF.patch {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hB : ∀ 𝔭, Submodule.IsLattice K (B 𝔭)) (hBs : ∀ 𝔭 ∉ s, B 𝔭 = L₀) :
    Submodule.IsLattice K (⨅ 𝔭, locF 𝔭.1 (B 𝔭)) ∧
      ∀ 𝔭, locF 𝔭.1 (⨅ 𝔮, locF 𝔮.1 (B 𝔮)) = locF 𝔭.1 (B 𝔭) := by sorry
