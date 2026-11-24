-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_redEnd_eq_iff
-- name    : Formalism.HermitianLattices.Ext.L3.D2.RedC.redEnd_eq_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:46:16.135326+00:00
-- url     : https://prove2.me/theorems/d285b038-6e97-4295-bae3-48f7dd5dcc68
-- title:
--   Red C: red End eq iff
-- statement:
--   The Red C construction uses the red End eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean#L39-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean#L39-L62

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
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
open Formalism.HermitianLattices.Ext.L3.D2.RedC

theorem Formalism.HermitianLattices.Ext.L3.D2.RedC.redEnd_eq_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a b : V ≃ₗ[K] V}
    (ha : a ∈ glSub A) (hb : b ∈ glSub A) :
    redEnd A 𝔭 k a ha = redEnd A 𝔭 k b hb ↔ a⁻¹ * b ∈ nSub A 𝔭 k := by sorry
