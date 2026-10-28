-- Prove2me | Theorems.Thm_Constructible_MostowskiCollapse_CondensationHull_exists_internalizedCollapse
-- name    : Constructible.MostowskiCollapse.CondensationHull.exists_internalizedCollapse
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T00:12:13.436759+00:00
-- url     : https://prove2.me/theorems/1e89e4e1-ba90-4c4e-9870-90abce206fba
-- title:
--   A condensation hull has a constructible collapse range and graph
-- statement:
--   Let $D\in L$ be a condensation hull at a condensation reflection level $L_\theta$: $D\subseteq L_\theta$, membership-formula satisfaction is absolute between the domain and that stage, and the fixed stage-history parameters belong to the domain. Then its Mostowski-collapse range $M$ and Kuratowski function graph $G$ are members of $L$:
--
--   $$
--   M\in L\quad\text{and}\quad G\in L.
--   $$
--
--   Equivalently, there exists internally represented collapse data for $D$. This allows the external collapse to be used in internal cardinal arguments.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.MostowskiCollapse.CondensationHull.exists_internalizedCollapse; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/GeneralCollapseInternalization.lean#L622.

import Definitions.Def_CH_ConstructibleGCH_Library05
set_option maxHeartbeats 2000000

universe u

theorem Constructible.MostowskiCollapse.CondensationHull.exists_internalizedCollapse : ∀ {theta : Ordinal.{u}} {domain : Constructible.Model.LCarrier.{u}},
  Constructible.MostowskiCollapse.CondensationHull.{u} theta
      (@Subtype.val.{u + 2} ZFSet.{u}
        (fun x =>
          @Membership.mem.{u + 1, u + 1} ZFSet.{u} (Set.{u + 1} ZFSet.{u}) (@Set.instMembership.{u + 1} ZFSet.{u})
            Constructible.L.{u} x)
        domain) →
    @Exists.{u + 2} (Constructible.Model.InternalizedCollapse.{u} domain) fun _witness => True := by sorry
