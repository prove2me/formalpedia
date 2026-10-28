-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_hartogsStageBound_lCarrier
-- name    : Constructible.ContinuumFormula.hartogsStageBound_lCarrier
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T00:03:47.857295+00:00
-- url     : https://prove2.me/theorems/a9c4a11c-4758-41a8-9b3d-b4c5d16ddbf4
-- title:
--   The Hartogs-stage cardinal bound in L
-- statement:
--   For every internal cardinal $\kappa\in L$ with $\omega\subseteq\kappa$, write $\kappa^+=H^L(\kappa)$. There is an injection with graph in $L$ satisfying
--
--   $$
--   L_{\kappa^+}\hookrightarrow\kappa^+.
--   $$
--
--   This bounds the size of the constructible stage used in the GCH argument.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.hartogsStageBound_lCarrier; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalLStageInjection.lean#L123.

import Definitions.Def_CH_ConstructibleGCH_Library05
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.hartogsStageBound_lCarrier : ∀ (kappa : Constructible.Model.LCarrier.{u}),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      Constructible.ContinuumFormula.HartogsStageBound.{u} kappa := by sorry
