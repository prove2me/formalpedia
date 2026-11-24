-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Main_fac_exists
-- name    : Formalism.L2.Th1.E.Main.fac_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:43.364047+00:00
-- url     : https://prove2.me/theorems/f79d0ba2-5b5d-4f92-8615-855e473601f9
-- title:
--   Main: fac exists
-- statement:
--   The Main construction uses the fac exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L41-L59

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
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
open Formalism.L2.Th1.E.Main

theorem Formalism.L2.Th1.E.Main.fac_exists (hF : FacShape) {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
    (W : WeierstrassCurve K) (hW : IntCurve W) {T : Type} [AddCommGroup T]
    (π : T →+ W.toAffine.Point) (hI : IntPts W π) (P Q : T) (hP : π P ≠ 0) (hQ : π Q ≠ 0) :
    ∃ e, UnitAt e (C (px W (π Q)) - xT W (π P)) := by sorry
