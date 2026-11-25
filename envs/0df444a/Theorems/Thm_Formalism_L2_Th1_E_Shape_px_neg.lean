-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Shape_px_neg
-- name    : Formalism.L2.Th1.E.Shape.px_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:32.595806+00:00
-- url     : https://prove2.me/theorems/db5c4466-bac3-4e18-8ff5-d89fe02445e4
-- title:
--   Shape: px neg
-- statement:
--   The Shape construction uses the px neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInvTDen.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInvTDen.lean#L36-L37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInvTDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Shape
variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

theorem Formalism.L2.Th1.E.Shape.px_neg (Q : W.toAffine.Point) : px W (-Q) = px W Q := by sorry
