-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_normD_mul_relIndex
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.normD_mul_relIndex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:26.576247+00:00
-- url     : https://prove2.me/theorems/855c2666-ede5-44e4-bd2e-26bc1c9f2752
-- title:
--   Ball B: norm D mul rel Index
-- statement:
--   The Ball B construction uses the norm D mul rel Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormSpanSingletonEq.lean#L63-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormSpanSingletonEq.lean#L63-L97

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
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

theorem Formalism.HermitianLattices.Ext.L3.BallB.normD_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    (hb : ∀ i, b i ∈ L)
    (hidx : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    normD h L * ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ w : InfinitePlace K, w (gdet h b) := by sorry
