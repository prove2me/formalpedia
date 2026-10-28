-- Prove2me | Theorems.Thm_Constructible_Model_canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators
-- name    : Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:44:59.06099+00:00
-- url     : https://prove2.me/theorems/f6c5e666-5f04-44e7-af71-4ed5d782fe97
-- title:
--   The canonical history bound from evaluator correctness
-- statement:
--   Assume the finite bare Gödel output evaluator is correct in $L_{\omega+1}$ and the bare evaluator is correct in every limit stage $L_\lambda$ with $\omega<\lambda$, using the fixed stage-history parameters. Then for every ordinal $\alpha$, the canonical bare history $H_\alpha$ satisfies
--
--   $$
--   H_\alpha\in L_{\alpha+\omega}.
--   $$
--
--   This places the history data within a controlled later stage of the constructible hierarchy.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalBareHistoryGlobal.lean#L43.

import Definitions.Def_CH_ConstructibleGCH_Library04
set_option maxHeartbeats 2000000

universe u

theorem Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators : Constructible.Model.FiniteBareGodelDefOutputCorrectIn.{u}
    (Constructible.LStageZF.{u}
      (@Order.succ.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u})
        Ordinal.instSuccOrder.{u} Ordinal.omega0.{u}))
    Constructible.Model.stageHistoryFixedParametersRaw.{u} →
  (∀ (limit : Ordinal.{u}),
      @Order.IsSuccLimit.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u})
          limit →
        @LT.lt.{u + 1} Ordinal.{u}
            (@Preorder.toLT.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
            Ordinal.omega0.{u} limit →
          Constructible.Model.BareGodelDefOutputCorrectIn.{u} (Constructible.LStageZF.{u} limit)
            Constructible.Model.stageHistoryFixedParametersRaw.{u}) →
    ∀ (ordinal : Ordinal.{u}),
      @Membership.mem.{u + 1, u + 1} ZFSet.{u} ZFSet.{u}
        (@SetLike.instMembership.{u + 1, u + 1} ZFSet.{u} ZFSet.{u} ZFSet.instSetLike.{u})
        (Constructible.LStageZF.{u}
          (@HAdd.hAdd.{u + 1, u + 1, u + 1} Ordinal.{u} Ordinal.{u} Ordinal.{u}
            (@instHAdd.{u + 1} Ordinal.{u} Ordinal.add.{u}) ordinal Ordinal.omega0.{u}))
        (Constructible.Model.canonicalBareHistory.{u} ordinal) := by sorry
