-- Prove2me | Theorems.Thm_ContinuumHypothesis_Constructible_models_ZF
-- name    : ContinuumHypothesis.Constructible.models_ZF
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-23T23:12:20.384995+00:00
-- url     : https://prove2.me/theorems/d546b3ef-8003-41d8-ae11-50190bda533b
-- title:
--   Constructible universe: the ZF axioms
-- statement:
--   The membership structure on the constructible universe satisfies every axiom of Zermelo–Fraenkel set theory:
--   $$ (L,\in)\models\mathrm{ZF}. $$
--   Here $L$ is the explicitly defined hierarchy over the ambient ZFC sets, including all its ordinal levels.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Andrew Marks, Set Theory, updated January 31, 2026, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf, pp. 86–87, Lemma 20.5.

import Definitions.Def_CH_Constructible
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Constructible

theorem models_ZF : Carrier ⊨ ZF := by sorry

end ContinuumHypothesis.Constructible
