-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_exists_det_span
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.exists_det_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:32.214869+00:00
-- url     : https://prove2.me/theorems/2468f104-fd70-4228-a1e7-eb2c213572ab
-- title:
--   Ball B: exists det span
-- statement:
--   The Ball B construction uses the exists det span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormSpanSingletonEq.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormSpanSingletonEq.lean#L13-L25

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
omit [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.BallB.exists_det_span (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V}
    (hx : ∀ i, x i ∈ Submodule.span (𝓞 K) (Set.range b)) :
    ∃ d : 𝓞 K, algebraMap (𝓞 K) K d = b.det x := by sorry
