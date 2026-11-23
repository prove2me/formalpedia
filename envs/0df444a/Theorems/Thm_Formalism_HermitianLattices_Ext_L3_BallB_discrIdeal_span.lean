-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_discrIdeal_span
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.discrIdeal_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:54.157534+00:00
-- url     : https://prove2.me/theorems/b9ec8e72-b537-4657-9045-e94b882bc2be
-- title:
--   Ball B: discr Ideal span
-- statement:
--   The Ball B construction uses the discr Ideal span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormSpanSingletonEq.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormSpanSingletonEq.lean#L27-L44

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.discrIdeal_span {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = gdet h b) :
    discrIdeal h (Submodule.span (𝓞 K) (Set.range b)) = Ideal.span {g₀} := by sorry
