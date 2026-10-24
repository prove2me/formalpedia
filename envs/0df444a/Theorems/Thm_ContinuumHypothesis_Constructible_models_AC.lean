-- Prove2me | Theorems.Thm_ContinuumHypothesis_Constructible_models_AC
-- name    : ContinuumHypothesis.Constructible.models_AC
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-23T23:11:55.116173+00:00
-- url     : https://prove2.me/theorems/f02557d7-a859-45e9-a7a5-64b8bdd6ae5d
-- title:
--   Constructible universe: axiom of choice
-- statement:
--   The constructible universe satisfies the axiom of choice:
--   $$ (L,\in)\models\mathrm{AC}. $$
--   This concerns choice functions belonging to $L$, with all quantifiers interpreted in its membership structure.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Andrew Marks, Set Theory, updated January 31, 2026, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf, p. 88, Theorem 20.9.

import Definitions.Def_CH_Constructible
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Constructible

theorem models_AC : Carrier ⊨ acSentence := by sorry

end ContinuumHypothesis.Constructible
