-- Prove2me | Theorems.Thm_ContinuumHypothesis_Cohen_ch_sentence_implies_expanded_CH
-- name    : ContinuumHypothesis.Cohen.ch_sentence_implies_expanded_CH
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:17:02.188484+00:00
-- url     : https://prove2.me/theorems/1b4f0910-6bbc-462f-8779-977fbc8ec821
-- title:
--   The mission’s CH sentence implies Flypitch’s CH sentence in an expanded ZFC model
-- statement:
--   Let $M$ be a nonempty ordinary model of Flypitch’s expanded ZFC presentation, including all strong Collection instances. If its membership reduct satisfies the mission’s existing CH sentence, then $M$ satisfies Flypitch’s native CH sentence:
--
--   $$M\mathbin{\upharpoonright}\{\in\}\models\mathrm{CH}_{\mathrm{mission}}\quad\Longrightarrow\quad M\models\mathrm{CH}_{\mathrm{expanded}}.$$
--
--   The mission sentence compares subsets of the power set of omega by injection. The expanded sentence compares ordinals with the designated omega and its power set using surjections from subsets. This one-way compatibility statement transports the native countermodel’s failure of CH to the mission sentence.
--
--   The original forcing formalization is by Jesse Han and Floris van Doorn. The Lean 4 port is by Ian Klatzco, with Claude, under Apache-2.0. This compatibility statement connects that development to the mission’s existing definitions.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, A Formal Proof of the Independence of the Continuum Hypothesis, CPP 2020, §2.2 and Figure 1, and §7 (the membership-language transfer is listed as future work), https://florisvandoorn.com/papers/flypitch-cpp-2020.pdf; Ian Klatzco Lean 4 port, commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815, Flypitch4/Zfc.lean; mission definitions CH_SetTheoryLanguage and CH_ZFC. Explicit semantic compatibility obligations for those two axiom and sentence presentations.

import Definitions.Def_CH_Cohen_Reduct

open FirstOrder FirstOrder.Language

theorem ContinuumHypothesis.Cohen.ch_sentence_implies_expanded_CH
    (M : Fol.Structure _root_.L_ZFC) (hM : Nonempty M.carrier)
    (hZFC : Fol.all_realize_sentence M _root_.ZFC)
    (hCH : letI : ContinuumHypothesis.setLang.Structure M.carrier :=
        ContinuumHypothesis.Cohen.membershipReduct M
      M.carrier ⊨ ContinuumHypothesis.chSentence) :
    Fol.realize_sentence M _root_.CH_f := by sorry
