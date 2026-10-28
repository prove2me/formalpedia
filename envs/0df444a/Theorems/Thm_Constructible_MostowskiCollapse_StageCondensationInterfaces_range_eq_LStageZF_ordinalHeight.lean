-- Prove2me | Theorems.Thm_Constructible_MostowskiCollapse_StageCondensationInterfaces_range_eq_LStageZF_ordinalHeight
-- name    : Constructible.MostowskiCollapse.StageCondensationInterfaces.range_eq_LStageZF_ordinalHeight
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:52:54.434997+00:00
-- url     : https://prove2.me/theorems/0cbcae68-742a-4945-a1af-007b2bc3528e
-- title:
--   The collapse range is the stage of its ordinal height
-- statement:
--   Let $D\subseteq L_\theta$ satisfy the stage-condensation interfaces: $\theta$ is a limit ordinal; membership-formula satisfaction is absolute between $D$ and $L_\theta$; $D$ contains the empty set; and the stage, internal-covering and smaller-stage witness conditions hold. If $M$ is the Mostowski-collapse range of $D$ and $\operatorname{ht}(M)$ is its ordinal height, then
--
--   $$
--   M=L_{\operatorname{ht}(M)}.
--   $$
--
--   This is the collapse-induction conclusion of the condensation interface.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.MostowskiCollapse.StageCondensationInterfaces.range_eq_LStageZF_ordinalHeight; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationAssembly.lean#L197.

import Definitions.Def_CH_ConstructibleGCH_Library04
set_option maxHeartbeats 2000000

universe u

theorem Constructible.MostowskiCollapse.StageCondensationInterfaces.range_eq_LStageZF_ordinalHeight : ∀ {theta : Ordinal.{u}} {domain : ZFSet.{u}},
  Constructible.MostowskiCollapse.StageCondensationInterfaces.{u} theta domain →
    @Eq.{u + 2} ZFSet.{u} (Constructible.MostowskiCollapse.range.{u} domain)
      (Constructible.LStageZF.{u} (Constructible.ordinalHeight.{u} (Constructible.MostowskiCollapse.range.{u} domain))) := by sorry
