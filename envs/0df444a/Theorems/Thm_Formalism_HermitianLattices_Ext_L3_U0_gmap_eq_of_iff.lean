-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_gmap_eq_of_iff
-- name    : Formalism.HermitianLattices.Ext.L3.U0.gmap_eq_of_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:04.624094+00:00
-- url     : https://prove2.me/theorems/34ba01b8-211b-4e35-88a0-8fc63d09f53c
-- title:
--   U0: gmap eq of iff
-- statement:
--   The U0 construction uses the gmap eq of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLocFOfVdZero.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLocFOfVdZero.lean#L59-L68

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
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
open Formalism.HermitianLattices.Ext.L3.U0
open WA
omit [NumberField K] [StarRing K] [FiniteDimensional K V]

theorem Formalism.HermitianLattices.Ext.L3.U0.gmap_eq_of_iff {g : V ≃ₗ[K] V} {A B : Submodule (𝓞 K) V} (hg : ∀ v, v ∈ A ↔ g v ∈ B) :
    Formalism.HermitianLatticesTheory.gmap g A = B := by sorry
