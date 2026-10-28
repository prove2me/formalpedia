-- Prove2me | Theorems.Thm_Constructible_Model_canonicalBareHistory_mem_LStageZF_add_omega
-- name    : Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:49:13.485995+00:00
-- url     : https://prove2.me/theorems/ad55d1e2-f3d5-4cf9-9e67-eb1dd406ee25
-- title:
--   Canonical stage histories belong to L at alpha plus omega
-- statement:
--   For every ordinal $\alpha$, let $H_\alpha$ be the canonical bare stage history with the fixed stage-history parameters. Then
--
--   $$
--   H_\alpha\in L_{\alpha+\omega}.
--   $$
--
--   The bound makes the canonical history available as a set at a specified constructible stage.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalBareHistoryGlobal.lean#L85.

import Definitions.Def_CH_ConstructibleGCH_Library03
set_option maxHeartbeats 2000000

universe u

theorem Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega : ∀ (ordinal : Ordinal.{u}),
  @Membership.mem.{u + 1, u + 1} ZFSet.{u} ZFSet.{u}
    (@SetLike.instMembership.{u + 1, u + 1} ZFSet.{u} ZFSet.{u} ZFSet.instSetLike.{u})
    (Constructible.LStageZF.{u}
      (@HAdd.hAdd.{u + 1, u + 1, u + 1} Ordinal.{u} Ordinal.{u} Ordinal.{u}
        (@instHAdd.{u + 1} Ordinal.{u} Ordinal.add.{u}) ordinal Ordinal.omega0.{u}))
    (Constructible.Model.canonicalBareHistory.{u} ordinal) := by sorry
