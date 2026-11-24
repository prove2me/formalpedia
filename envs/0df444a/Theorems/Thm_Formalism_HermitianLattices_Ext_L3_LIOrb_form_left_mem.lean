-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_form_left_mem
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.form_left_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:25.86391+00:00
-- url     : https://prove2.me/theorems/309b4775-1e5c-41d2-abaf-9a998045bb17
-- title:
--   LIOrb: form left mem
-- statement:
--   The LIOrb construction uses the form left mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L140-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L140-L152

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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.form_left_mem (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {A : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hAi : IsIntegralAt 𝔭 h A)
    {k : ℕ} {y z : V} (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) :
    h z y ∈ D2.pK K 𝔭 k := by sorry
