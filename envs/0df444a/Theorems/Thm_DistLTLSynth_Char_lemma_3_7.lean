-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_7
-- name    : DistLTLSynth.Char.lemma_3_7
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T09:13:12.066416+00:00
-- url     : https://prove2.me/theorems/ba0bad50-5f7d-4dc0-af2a-2f2bd7b84a40
-- title:
--   Lemma 3.7: Executable Block Automaton and Live State Construction
-- statement:
--   Executable construction of the deterministic parity block automaton $\mathcal{B}$ and its live state set $Q_{\mathrm{live}}$ (Lemma 3.7).
--
--   Given a primitive-recursive B\u00fcchi-to-parity determinizer, an adversary deterministic parity automaton code $c$ recognizing $A = \mathcal{L}(c) \subseteq \Gamma^\omega$, a synthesis instance $I$ whose token list parses to an LTL formula $\varphi$, and a positive block length $D = D_0 + 1 \ge 1$, one can primitive-recursively construct a finite deterministic parity automaton $\mathcal{B}$ over block alphabet $\Sigma^D \times \Omega^D$ together with a decidable subset $Q_{\mathrm{live}} \subseteq Q_{\mathcal{B}}$ such that for every execution $e \in (\Sigma \times \Omega)^\omega$ and block index $n \in \mathbb{N}$:
--
--   $$
--   \mathcal{B}\text{ accepts }\mathrm{toBlocks}_D(e) \iff \bigl(\mathrm{Graph}(e) \notin A \lor e \models \varphi\bigr), \qquad \mathrm{run}_{\mathcal{B}}(\mathrm{toBlocks}_D(e), n) \in Q_{\mathrm{live}} \iff \mathrm{Graph}(e)[\dots nD] \in \mathrm{Pref}(A).
--   $$
--
--   This theorem formalizes Lemma 3.7 of the source paper, reducing distributed LTL synthesis over $D$-round consensus blocks to parity acceptance of component trees.
--
--   **Formalization Note** The finite block alphabet $\mathrm{Fin}\,D \to \Sigma \times \Omega$ is bridged to the code interface $\mathrm{GenDPACode}$ via the primitive-recursive block encoder `encIOBlockNat` and its typed counterpart `encIOBlockTyped`.
-- source:
--   arXiv:2611.04561, Distributed LTL Synthesis under Arbitrary Message Adversaries, Section 3.3, Lemma 3.7 (p. 13)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

namespace DistLTLSynth.Char

theorem lemma_3_7 :
    (∃ detNBW : ℕ → NBWCode → GenDPACode, Primrec₂ detNBW ∧
      ∀ (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)),
        (toGenDPA αSize (detNBW αSize b)).Accepts w ↔ NBWAccepts αSize b w) →
    ∃ (blockAlphaMinusOne : Instance → ℕ → ℕ)
      (encIOBlockNat : Instance → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ)
      (encIOBlockTyped : ∀ (I : Instance) (D : ℕ),
        (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) → Fin (blockAlphaMinusOne I D + 1))
      (compileBlock : DPACode × Instance × ℕ → GenDPACode × List Bool),
      Primrec₂ blockAlphaMinusOne ∧
      (Primrec fun p : (Instance × ℕ) × List (ℕ × ℕ × ℕ × ℕ × ℕ) =>
        encIOBlockNat p.1.1 p.1.2 p.2) ∧
      (∀ (I : Instance) (D : ℕ) (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)),
        (encIOBlockTyped I D blk).val =
          encIOBlockNat I D
            ((List.ofFn blk).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) %
            (blockAlphaMinusOne I D + 1)) ∧
      Primrec compileBlock ∧
      (∀ (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ),
        parse I.tokens = some φ →
          let D := D_m1 + 1
          let res := compileBlock (c, I, D_m1)
          let dpa := toGenDPA (blockAlphaMinusOne I D) res.1
          let B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
            ⟨dpa.init, fun q blk => dpa.step q (encIOBlockTyped I D blk), dpa.prio⟩
          let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
          IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive) := by sorry

end DistLTLSynth.Char
