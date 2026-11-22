-- Prove2me | Theorems.Thm_DistLTLSynth_Char_nbw_determinization
-- name    : DistLTLSynth.Char.nbw_determinization
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T09:13:07.216091+00:00
-- url     : https://prove2.me/theorems/c0f114a8-4205-4c21-8c14-3cecc2c8e62d
-- title:
--   Primitive-Recursive Determinization of Nondeterministic Büchi Automata to DPAs
-- statement:
--   Primitive-recursive determinization of finite nondeterministic B\u00fcchi automata into finite state-based deterministic parity automata over indexed finite alphabets $\mathrm{Fin}(\alpha + 1)$.
--
--   Given an alphabet bound $\alpha \in \mathbb{N}$ and a finite nondeterministic B\u00fcchi automaton encoded either via transition bitmasks ($B \in \mathrm{NBWCode}$) or adjacency lists ($B \in \mathrm{ListNBWCode}$), there exist primitive-recursive compilers $\mathrm{detNBW}$ and $\mathrm{detListNBW}$ producing deterministic parity automaton codes in $\mathrm{GenDPACode}$ that recognize the exact same $\omega$-language:
--
--   $$
--   \mathcal{L}\bigl(\mathrm{toGenDPA}(\alpha, \mathrm{detNBW}(\alpha, B))\bigr) = \mathcal{L}_{\mathrm{NBW}}(\alpha, B).
--   $$
--
--   This theorem supplies the $\omega$-regular determinization engine needed both to compile LTL specifications and adversary complements into deterministic parity block automata (Lemma 3.7) and to determinize universal edge-thread parity monitors on symbolic component trees (Theorem 3.4).
--
--   **Formalization Note** Both bitmask (`NBWCode`) and list-based (`ListNBWCode`) encodings are provided so downstream constructions can work with whichever representation matches their transition tables.
-- source:
--   arXiv:2611.04561, Distributed LTL Synthesis under Arbitrary Message Adversaries, Section 3.3 (Lemma 3.7, p. 13) and Section 7 (Definition 7.6)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

namespace DistLTLSynth.Char

theorem nbw_determinization :
    (∃ detNBW : ℕ → NBWCode → GenDPACode, Primrec₂ detNBW ∧
      ∀ (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)),
        (toGenDPA αSize (detNBW αSize b)).Accepts w ↔ NBWAccepts αSize b w) ∧
    (∃ detListNBW : ℕ → ListNBWCode → GenDPACode, Primrec₂ detListNBW ∧
      ∀ (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)),
        (toGenDPA αSize (detListNBW αSize B)).Accepts w ↔ ListNBWAccepts αSize B w) := by sorry

end DistLTLSynth.Char
