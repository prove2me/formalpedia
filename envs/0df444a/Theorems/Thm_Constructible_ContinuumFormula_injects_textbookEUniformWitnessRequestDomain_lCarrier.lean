-- Prove2me | Theorems.Thm_Constructible_ContinuumFormula_injects_textbookEUniformWitnessRequestDomain_lCarrier
-- name    : Constructible.ContinuumFormula.injects_textbookEUniformWitnessRequestDomain_lCarrier
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T00:00:55.63036+00:00
-- url     : https://prove2.me/theorems/85bb9a57-e284-49b7-aa70-b8f3665e40f4
-- title:
--   Uniform witness requests preserve the internal size bound
-- statement:
--   Let $\kappa$ be an infinite internal cardinal of $L$ and let $S\in L$ admit an internal injection into $\kappa$. The coded request domain $R(S)$ for the textbook E uniform-witness operation admits an internal injection
--
--   $$
--   R(S)\hookrightarrow\kappa.
--   $$
--
--   This controls the size of the requests used to close a seed under the specified definability witnesses.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53, theorem Constructible.ContinuumFormula.injects_textbookEUniformWitnessRequestDomain_lCarrier; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEUniformWitnessCardinality.lean#L66.

import Definitions.Def_CH_ConstructibleGCH_Library26
set_option maxHeartbeats 2000000

universe u

theorem Constructible.ContinuumFormula.injects_textbookEUniformWitnessRequestDomain_lCarrier : ∀ {seed kappa : Constructible.Model.LCarrier.{u}},
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
          Constructible.Model.lCarrierMem.{u} seed kappa →
        @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
          Constructible.Model.lCarrierMem.{u} (Constructible.Model.textbookEUniformWitnessRequestDomain.{u} seed) kappa := by sorry
