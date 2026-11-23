-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mixed_mem
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.mixed_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:24.089239+00:00
-- url     : https://prove2.me/theorems/ff202226-5611-4c8d-a973-bba959189a47
-- title:
--   Ball B: mixed mem
-- statement:
--   The Ball B construction uses the mixed mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L95-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L95-L129

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.mixed_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {x : Fin (finrank K V) → V} {i : Fin (finrank K V)} (hx : ∀ k, k ≠ i → x k ∈ L) {y y' : V}
    (hy : y ∈ L) (hy' : y' ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det (Function.update x i y)) * gdet h b *
      b.det (Function.update x i y')) : z ∈ discrIdeal h L := by sorry
