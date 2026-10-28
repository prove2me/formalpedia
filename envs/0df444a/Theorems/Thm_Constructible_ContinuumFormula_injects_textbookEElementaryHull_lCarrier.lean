-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_injects_textbookEElementaryHull_lCarrier
-- name    : Constructible.ContinuumFormula.injects_textbookEElementaryHull_lCarrier
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T00:27:35.454591+00:00
-- url     : https://prove2.me/theorems/fda7300e-caaa-4019-9a98-b779ed5b6971
-- title:
--   The textbook E elementary hull has internal size at most kappa
-- statement:
--   Let $\kappa,x\in L$, with $\kappa$ an internal cardinal satisfying $\omega\subseteq\kappa$. The canonical textbook E elementary hull $H(\kappa,x)$ admits an injection represented inside $L$:
--
--   $$
--   H(\kappa,x)\hookrightarrow\kappa.
--   $$
--
--   This provides the internal size bound for the hull used in the condensation proof.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.injects_textbookEElementaryHull_lCarrier; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEUniformWitnessCardinality.lean#L173.

import Definitions.Def_CH_ConstructibleGCH_HullIteration
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.injects_textbookEElementaryHull_lCarrier : ∀ (kappa x : Constructible.Model.LCarrier.{u}),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} (Constructible.ContinuumFormula.textbookEElementaryHull.{u} kappa x) kappa := by sorry
