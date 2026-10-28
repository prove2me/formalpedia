-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_CardinalControlledHull_element_mem_internalHartogsStage
-- name    : Constructible.ContinuumFormula.CardinalControlledHull.element_mem_internalHartogsStage
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:57:18.627655+00:00
-- url     : https://prove2.me/theorems/cac4a3e5-b5bb-4a2e-a93c-9ac6801dce8e
-- title:
--   A controlled subset belongs below the Hartogs stage
-- statement:
--   Let $\kappa$ be an internal cardinal of $L$ and let $x\in L$ satisfy $x\subseteq\kappa$. Given cardinal-controlled hull data for $(\kappa,x)$, with an internal injection of the hull domain into $\kappa$ and an internally represented collapse,
--
--   $$
--   x\in L_{H^L(\kappa)}.
--   $$
--
--   Here $H^L(\kappa)$ is the internal Hartogs ordinal. The assertion bounds the stage at which this constructible subset occurs.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.CardinalControlledHull.element_mem_internalHartogsStage; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationGCHBridge.lean#L240.

import Definitions.Def_CH_ConstructibleGCH_Library05
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.CardinalControlledHull.element_mem_internalHartogsStage : ∀ {kappa x : Constructible.Model.LCarrier.{u}} (h : Constructible.ContinuumFormula.CardinalControlledHull.{u} kappa x),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} x kappa →
      @Membership.mem.{u + 1, u + 1} ZFSet.{u} ZFSet.{u}
        (@SetLike.instMembership.{u + 1, u + 1} ZFSet.{u} ZFSet.{u} ZFSet.instSetLike.{u})
        (Constructible.LStageZF.{u} (Constructible.ContinuumFormula.internalHartogsOrdinal.{u} kappa))
        (@Subtype.val.{u + 2} ZFSet.{u}
          (fun x =>
            @Membership.mem.{u + 1, u + 1} ZFSet.{u} (Set.{u + 1} ZFSet.{u}) (@Set.instMembership.{u + 1} ZFSet.{u})
              Constructible.L.{u} x)
          x) := by sorry
