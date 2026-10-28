-- Prove2me | Theorems.Thm_ContinuumHypothesis_Cohen_membership_reduct_models_ZFC
-- name    : ContinuumHypothesis.Cohen.membership_reduct_models_ZFC
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:14:01.441894+00:00
-- url     : https://prove2.me/theorems/7cf423b7-8e70-4518-a4b0-f5cdfae84127
-- title:
--   Removing the expanded symbols preserves the mission’s exact ZFC theory
-- statement:
--   Let $M$ be a nonempty ordinary model of Flypitch’s expanded ZFC presentation, including all of its strong Collection instances. Forget its five function symbols and retain its membership relation. The resulting structure satisfies the mission’s existing membership-language ZFC theory:
--
--   $$M\models T_{\mathrm{expanded}}\quad\Longrightarrow\quad M\mathbin{\upharpoonright}\{\in\}\models T_{\mathrm{mission}}.$$
--
--   The conclusion includes the exact Separation and Replacement schemas and the mission’s choice-set sentence. This is the axiom-transfer obligation required to use the expanded Cohen countermodel in this mission.
--
--   The original forcing formalization is by Jesse Han and Floris van Doorn. The Lean 4 port is by Ian Klatzco, with Claude, under Apache-2.0. This compatibility statement connects that development to the mission’s existing definitions.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, A Formal Proof of the Independence of the Continuum Hypothesis, CPP 2020, §2.2 and Figure 1, and §7 (the membership-language transfer is listed as future work), https://florisvandoorn.com/papers/flypitch-cpp-2020.pdf; Ian Klatzco Lean 4 port, commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815, Flypitch4/Zfc.lean; mission definitions CH_SetTheoryLanguage and CH_ZFC. Explicit semantic compatibility obligations for those two axiom and sentence presentations.

import Definitions.Def_CH_Cohen_Reduct

open FirstOrder FirstOrder.Language

theorem ContinuumHypothesis.Cohen.membership_reduct_models_ZFC
    (M : Fol.Structure _root_.L_ZFC) (hM : Nonempty M.carrier)
    (hZFC : Fol.all_realize_sentence M _root_.ZFC) :
    letI : ContinuumHypothesis.setLang.Structure M.carrier :=
      ContinuumHypothesis.Cohen.membershipReduct M
    M.carrier ⊨ ContinuumHypothesis.ZFC := by sorry
