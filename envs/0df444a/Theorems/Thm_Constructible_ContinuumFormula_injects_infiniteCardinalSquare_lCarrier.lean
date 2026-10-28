-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_injects_infiniteCardinalSquare_lCarrier
-- name    : Constructible.ContinuumFormula.injects_infiniteCardinalSquare_lCarrier
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-25T23:57:13.625894+00:00
-- url     : https://prove2.me/theorems/d874ca43-9754-460a-954a-f30a7ee33a7b
-- title:
--   An infinite internal cardinal absorbs its square
-- statement:
--   Let $\kappa\in L$ be an internal cardinal with $\omega\subseteq\kappa$. There is an injection of $\kappa\times\kappa$ into $\kappa$ whose function graph belongs to $L$:
--
--   $$
--   L\models\kappa\times\kappa\hookrightarrow\kappa.
--   $$
--
--   This is internal cardinal arithmetic; the representing graph is part of the assertion.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.injects_infiniteCardinalSquare_lCarrier; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalInfiniteCardinalSquare.lean#L286.

import Definitions.Def_CH_ConstructibleGCH_Library05
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.injects_infiniteCardinalSquare_lCarrier : ∀ {kappa : Constructible.Model.LCarrier.{u}},
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} (Constructible.Model.prodLCarrier.{u} kappa kappa) kappa := by sorry
