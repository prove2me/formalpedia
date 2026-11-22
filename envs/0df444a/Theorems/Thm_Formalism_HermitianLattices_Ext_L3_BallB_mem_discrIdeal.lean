-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mem_discrIdeal
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.mem_discrIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:01.367809+00:00
-- url     : https://prove2.me/theorems/80da408f-7095-4a36-970c-28afeb53857e
-- title:
--   Ball B: mem discr Ideal
-- statement:
--   The Ball B construction uses the mem discr Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L39-L42

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.mem_discrIdeal {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V} (hx : ∀ i, x i ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x) : z ∈ discrIdeal h L := by sorry
