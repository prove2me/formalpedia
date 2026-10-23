-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_sentence_implies_ch_sentence
-- name    : ContinuumHypothesis.gch_sentence_implies_ch_sentence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:27:27.344091+00:00
-- url     : https://prove2.me/theorems/a12ee503-d5da-4e45-bb64-1987426529bd
-- title:
--   GCH implies CH (over ZFC)
-- statement:
--   The continuum hypothesis is the special case $S=\omega$ of the generalized continuum hypothesis: every model of
--   $$\mathrm{ZFC}+\mathrm{GCH}$$
--   satisfies $\mathrm{CH}$.
--
--   Together with Gödel's consistency theorem this gives $\mathrm{Con}(\mathrm{ZF})\Rightarrow\mathrm{Con}(\mathrm{ZFC}+\mathrm{CH})$.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Generalized continuum hypothesis' ('The continuum hypothesis is the special case for the ordinal α = 1', 'As GCH implies CH, …').

import Definitions.Def_CH_ZFC
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis

theorem gch_sentence_implies_ch_sentence : (ZFC ∪ {gchSentence}) ⊨ᵇ chSentence := by sorry

end ContinuumHypothesis
