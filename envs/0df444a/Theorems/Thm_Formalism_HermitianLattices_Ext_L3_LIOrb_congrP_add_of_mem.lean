-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_congrP_add_of_mem
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.congrP_add_of_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:24.323579+00:00
-- url     : https://prove2.me/theorems/6ba7d215-6bc0-44ec-8e36-e1975a109d43
-- title:
--   LIOrb: congr P add of mem
-- statement:
--   The LIOrb construction uses the congr P add of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L154-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L154-L165

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.congrP_add_of_mem (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {A : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hAi : IsIntegralAt 𝔭 h A)
    {k : ℕ} {y z : V} (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) {c : K}
    (hc : CongrP 𝔭 k (h y y) c) : CongrP 𝔭 k (h (y + z) (y + z)) c := by sorry
