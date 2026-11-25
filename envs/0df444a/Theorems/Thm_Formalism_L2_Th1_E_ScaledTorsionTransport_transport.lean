-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ScaledTorsionTransport_transport
-- name    : Formalism.L2.Th1.E.ScaledTorsionTransport.transport
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:48.385401+00:00
-- url     : https://prove2.me/theorems/8eec1a83-9838-5099-831e-3a5af9bb498d
-- title:
--   Scaled Torsion Transport: transport
-- statement:
--   The Scaled Torsion Transport construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledTorsionPointNonsingular.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledTorsionPointNonsingular.lean#L13-L18

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledTorsionPointNonsingular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.ScaledTorsionTransport

theorem Formalism.L2.Th1.E.ScaledTorsionTransport.transport {K : Type*} [Field K] [DecidableEq K] {W W' : WeierstrassCurve K} (hW : W = W')
    {x y x' y' : K} (hx : x = x') (hy : y = y') (h : W.toAffine.Nonsingular x y) (N : ℕ)
    (hN : N • WeierstrassCurve.Affine.Point.some _ _ h = 0) :
    ∃ h' : W'.toAffine.Nonsingular x' y', N • WeierstrassCurve.Affine.Point.some _ _ h' = 0 := by sorry
