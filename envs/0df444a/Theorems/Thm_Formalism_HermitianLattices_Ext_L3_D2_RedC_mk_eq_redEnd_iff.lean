-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_mk_eq_redEnd_iff
-- name    : Formalism.HermitianLattices.Ext.L3.D2.RedC.mk_eq_redEnd_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:01.516315+00:00
-- url     : https://prove2.me/theorems/94181dc2-643d-45b2-a0e0-4d8d22cc0d18
-- title:
--   Red C: mk eq red End iff
-- statement:
--   The Red C construction uses the mk eq red End iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean#L32-L37

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

theorem Formalism.HermitianLattices.Ext.L3.D2.RedC.mk_eq_redEnd_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ glSub A) (x x' : ↥A) :
    Submodule.Quotient.mk x' = redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) ↔
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by sorry
