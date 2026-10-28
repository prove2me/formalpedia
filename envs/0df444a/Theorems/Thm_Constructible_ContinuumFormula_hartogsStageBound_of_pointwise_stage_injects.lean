-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_hartogsStageBound_of_pointwise_stage_injects
-- name    : Constructible.ContinuumFormula.hartogsStageBound_of_pointwise_stage_injects
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T00:00:34.94565+00:00
-- url     : https://prove2.me/theorems/af82fec8-fdef-4aa3-b854-6c93d5408c23
-- title:
--   Pointwise stage injections give the Hartogs-stage bound
-- statement:
--   Let $\kappa$ be an infinite internal cardinal of $L$, and write $\kappa^+=H^L(\kappa)$. Assume that for every $\alpha<\kappa^+$ there is an internal injection $L_\alpha\hookrightarrow\kappa$. Then there is an internal injection
--
--   $$
--   L_{\kappa^+}\hookrightarrow\kappa^+.
--   $$
--
--   All injection witnesses are function graphs in $L$. This packages the cardinal bound at the Hartogs stage.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.hartogsStageBound_of_pointwise_stage_injects; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalStageInjectionFamily.lean#L360.

import Definitions.Def_CH_ConstructibleGCH_Library05
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.hartogsStageBound_of_pointwise_stage_injects : ∀ (kappa : Constructible.Model.LCarrier.{u}),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      (∀ (ordinal : Ordinal.{u}),
          @LT.lt.{u + 1} Ordinal.{u}
              (@Preorder.toLT.{u + 1} Ordinal.{u}
                (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
              ordinal (Constructible.ContinuumFormula.internalHartogsOrdinal.{u} kappa) →
            @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
              Constructible.Model.lCarrierMem.{u} (Constructible.Model.stageLCarrier.{u} ordinal) kappa) →
        Constructible.ContinuumFormula.HartogsStageBound.{u} kappa := by sorry
