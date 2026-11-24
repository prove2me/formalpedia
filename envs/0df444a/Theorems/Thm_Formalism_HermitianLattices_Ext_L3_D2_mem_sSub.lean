-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_sSub
-- name    : Formalism.HermitianLattices.Ext.L3.D2.mem_sSub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:34:00.910994+00:00
-- url     : https://prove2.me/theorems/bf0c377a-ae81-42ba-ba7e-4a11898c2247
-- title:
--   D2: mem s Sub
-- statement:
--   The D2 construction uses the mem s Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmul.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmul.lean#L79-L81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
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
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.D2.mem_sSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    {X : V ≃ₗ[K] V} : X ∈ sSub h A 𝔭 k ↔
      X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k := by sorry
