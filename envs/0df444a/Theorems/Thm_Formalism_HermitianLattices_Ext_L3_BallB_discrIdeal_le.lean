-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_discrIdeal_le
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.discrIdeal_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:10.392508+00:00
-- url     : https://prove2.me/theorems/bf0b16a9-dd38-43c4-8855-2cd1e78b5cfd
-- title:
--   Ball B: discr Ideal le
-- statement:
--   The Ball B construction uses the discr Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L44-L50

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.discrIdeal_le {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {I : Ideal (𝓞 K)}
    (hI : ∀ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) → ∀ z : 𝓞 K,
      algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x → z ∈ I) : discrIdeal h L ≤ I := by sorry
