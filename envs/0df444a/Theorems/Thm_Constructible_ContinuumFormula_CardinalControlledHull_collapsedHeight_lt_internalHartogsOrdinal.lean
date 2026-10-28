-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_CardinalControlledHull_collapsedHeight_lt_internalHartogsOrdinal
-- name    : Constructible.ContinuumFormula.CardinalControlledHull.collapsedHeight_lt_internalHartogsOrdinal
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:04:34.128538+00:00
-- url     : https://prove2.me/theorems/bc8165d7-b25c-4898-b12d-10580d673d0c
-- title:
--   A cardinal-controlled collapse lies below the Hartogs ordinal
-- statement:
--   Let $\kappa,x\in L$, and let $h$ be cardinal-controlled hull data: its constructible domain contains every element of $\kappa$ and contains $x$ as an element, is an elementary hull at a condensation reflection level, has an internal injection into $\kappa$, and has an internally represented Mostowski collapse. If $\alpha_h$ is the ordinal height of the collapse range and $H^L(\kappa)$ is the internal Hartogs ordinal, then
--
--   $$
--   \alpha_h<H^L(\kappa).
--   $$
--
--   This bounds the ordinal index of the collapsed constructible stage.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.CardinalControlledHull.collapsedHeight_lt_internalHartogsOrdinal; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationGCHBridge.lean#L198.

import Definitions.Def_CH_ConstructibleGCH_Library05
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.CardinalControlledHull.collapsedHeight_lt_internalHartogsOrdinal : ∀ {kappa x : Constructible.Model.LCarrier.{u}} (h : Constructible.ContinuumFormula.CardinalControlledHull.{u} kappa x),
  @LT.lt.{u + 1} Ordinal.{u}
    (@Preorder.toLT.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
    (@Constructible.ContinuumFormula.CardinalControlledHull.collapsedHeight.{u} kappa x h)
    (Constructible.ContinuumFormula.internalHartogsOrdinal.{u} kappa) := by sorry
