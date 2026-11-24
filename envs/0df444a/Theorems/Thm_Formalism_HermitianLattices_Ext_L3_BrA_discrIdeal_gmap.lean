-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_discrIdeal_gmap
-- name    : Formalism.HermitianLattices.Ext.L3.BrA.discrIdeal_gmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:19.115896+00:00
-- url     : https://prove2.me/theorems/c6c72400-2b90-4a97-b340-aa33cd7ee74d
-- title:
--   Br A: discr Ideal gmap
-- statement:
--   The Br A construction uses the discr Ideal gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L102-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L102-L126

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BrA.discrIdeal_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g A) = discrIdeal h A := by sorry
