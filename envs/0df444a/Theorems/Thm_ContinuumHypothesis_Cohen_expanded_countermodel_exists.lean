-- Prove2me | Theorems.Thm_ContinuumHypothesis_Cohen_expanded_countermodel_exists
-- name    : ContinuumHypothesis.Cohen.expanded_countermodel_exists
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:04:20.280087+00:00
-- url     : https://prove2.me/theorems/7f689aa0-85d7-4bee-b342-21b5b646e60b
-- title:
--   An ordinary countermodel to CH in Flypitch’s expanded set-theory language
-- statement:
--   Write $T_{\mathrm{expanded}}$ for Flypitch’s expanded ZFC theory and $\psi_{\mathrm{expanded}}$ for its CH sentence. There is a nonempty ordinary first-order structure $M$ for that expanded language such that
--
--   $$M\models T_{\mathrm{expanded}}\quad\text{and}\quad M\not\models\psi_{\mathrm{expanded}}.$$
--
--   This is an ordinary model-existence result obtained in Lean’s ambient metatheory. The language and axiom presentation are the native ones; removing the extra symbols and identifying the CH formula with the mission’s existing definitions are separate transfer theorems.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, CPP 2020, §§2.2–3 and 7; native CH unprovability: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Zfc.lean#L775-L776; native completeness/model existence: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Completeness.lean#L50-L72

import Definitions.Def_CH_Cohen_Library10
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem ContinuumHypothesis.Cohen.expanded_countermodel_exists : @Exists.{3} (Fol.Structure.{1} L_ZFC) fun M =>
  And (Nonempty.{2} (@Fol.Structure.carrier.{1} L_ZFC M))
    (And (@Fol.all_realize_sentence.{1} L_ZFC M ZFC) (Not (@Fol.realize_sentence.{1} L_ZFC M CH_f))) := by sorry
