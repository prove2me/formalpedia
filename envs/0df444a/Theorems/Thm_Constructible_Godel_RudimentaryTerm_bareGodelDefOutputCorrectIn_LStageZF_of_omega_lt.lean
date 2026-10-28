-- Prove2me | Theorems.Thm_Constructible_Godel_RudimentaryTerm_bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
-- name    : Constructible.Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:40:08.038899+00:00
-- url     : https://prove2.me/theorems/e1f25739-7692-43c7-878f-a797999d4bcf
-- title:
--   Correctness of the fixed Gödel evaluator above omega
-- statement:
--   Let $\theta$ be a limit ordinal with $\omega<\theta$. For the fixed stage-history parameters, the bare Gödel definable-output evaluator is correct when interpreted in $L_\theta$:
--
--   $$
--   \operatorname{BareGodelDefOutputCorrectIn}(L_\theta,\mathrm{fixedParameters}).
--   $$
--
--   This is the evaluator interface used to interpret canonical stage histories at large limit stages.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/BareGodelDefAbsolute.lean#L2248.

import Definitions.Def_CH_ConstructibleGCH_Library02
set_option maxHeartbeats 2000000

universe u

theorem Constructible.Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt : ∀ {theta : Ordinal.{u}},
  @Order.IsSuccLimit.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}) theta →
    @LT.lt.{u + 1} Ordinal.{u}
        (@Preorder.toLT.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
        Ordinal.omega0.{u} theta →
      Constructible.Model.BareGodelDefOutputCorrectIn.{u} (Constructible.LStageZF.{u} theta)
        Constructible.Model.stageHistoryFixedParametersRaw.{u} := by sorry
