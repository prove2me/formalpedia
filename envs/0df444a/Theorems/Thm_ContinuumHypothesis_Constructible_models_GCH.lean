-- Prove2me | Theorems.Thm_ContinuumHypothesis_Constructible_models_GCH
-- name    : ContinuumHypothesis.Constructible.models_GCH
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-23T23:11:55.021231+00:00
-- url     : https://prove2.me/theorems/6743723b-9415-45e2-9393-64e7efbb2528
-- title:
--   Constructible universe: generalized continuum hypothesis
-- statement:
--   The constructible universe satisfies the generalized continuum hypothesis:
--   $$ (L,\in)\models\mathrm{GCH}. $$
--   Cardinal comparisons and power sets are interpreted internally to $L$, rather than in the ambient universe.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Andrew Marks, Set Theory, updated January 31, 2026, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf, pp. 90–91, Lemma 21.3 and Corollary 21.4.

import Definitions.Def_CH_Constructible
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Constructible

theorem models_GCH : Carrier ⊨ gchSentence := by sorry

end ContinuumHypothesis.Constructible
