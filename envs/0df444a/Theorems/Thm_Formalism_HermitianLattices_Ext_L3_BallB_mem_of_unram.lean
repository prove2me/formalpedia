-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mem_of_unram
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.mem_of_unram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:13.208867+00:00
-- url     : https://prove2.me/theorems/c4b7a299-5e3a-49f6-8cb2-9bcf8684cce6
-- title:
--   Ball B: mem of unram
-- statement:
--   The Ball B construction uses the mem of unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L73-L93

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BallB.mem_of_unram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {I : Ideal (𝓞 K)} {z : 𝓞 K}
    (hz : ∀ θ : 𝓞 K, (θ - conjO K θ) * z ∈ I) : z ∈ I := by sorry
