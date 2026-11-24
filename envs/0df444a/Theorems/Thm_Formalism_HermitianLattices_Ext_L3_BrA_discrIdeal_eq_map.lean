-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_discrIdeal_eq_map
-- name    : Formalism.HermitianLattices.Ext.L3.BrA.discrIdeal_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:43.151059+00:00
-- url     : https://prove2.me/theorems/6e0039a7-371d-41c6-8647-a8e2e77665a2
-- title:
--   Br A: discr Ideal eq map
-- statement:
--   The Br A construction uses the discr Ideal eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L69-L86

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

theorem Formalism.HermitianLattices.Ext.L3.BrA.discrIdeal_eq_map (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) :
    discrIdeal h L = (discrF F h L).map (algebraMap (𝓞 F) (𝓞 K)) := by sorry
