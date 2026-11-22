-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_12
-- name    : DistLTLSynth.Char.lemma_3_12
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T12:45:23.726203+00:00
-- url     : https://prove2.me/theorems/c94e7ee6-3634-4791-8d56-d29f0c646443
-- title:
--   Forward completeness of compressed symbolic component trees (Lemma 3.12)
-- statement:
--   Let $c$ be a deterministic parity automaton code defining a message adversary $A = \mathcal{L}(c) \subseteq \Gamma^\omega$ with $\varepsilon \in \mathrm{Pref}(A)$, let $I$ be a distributed synthesis instance whose token list parses to an LTL formula $\varphi$, and let $D = D_0 + 1 \ge 1$ be a uniform binary-consensus horizon such that binary consensus is solvable within $D$ rounds under every live left quotient $g^{-1}A$ ($g \in \mathrm{Pref}(A)$). Let $(\mathcal{B}, Q_{\mathrm{live}})$ be the deterministic parity $D$-block automaton compiled from $(c, I, D - 1)$, and let $\mathcal{T}(I, D, \mathcal{B})$ be the corresponding compressed symbolic component-tree parity specification with retraction bound $B_{\mathrm{red}} = (1 + |Q_{\mathcal{B}}|)^{|\Sigma|^D} \cdot |\Sigma|^D$.
--
--   If $(\mathcal{B}, Q_{\mathrm{live}})$ admits an accepting uncompressed component tree $t_0$, then $\mathcal{T}(I, D, \mathcal{B})$ admits a valid accepting compressed symbolic tree, and therefore the regular tree parity game solver returns a winning strategy:
--
--   $$
--   \bigl(\exists t_0,\; \mathrm{IsUncompressedComponentTree}(\mathcal{B}, Q_{\mathrm{live}}, t_0) \land \mathrm{IsAcceptingTree}(\mathcal{B}, t_0)\bigr) \implies \mathrm{solveTreePG}\bigl(\mathcal{T}(I, D, \mathcal{B})\bigr) \neq \mathrm{none}.
--   $$
--
--   This theorem establishes the forward completeness direction of component-tree compression, showing that bounding compressed positions to $B_{\mathrm{full}} = B_{\mathrm{red}} \cdot |\Sigma|^D$ edges via endpoint-table retractions preserves the existence of winning strategies whenever uniform $D$-round consensus holds.
--
--   **Formalization Note** In Lean, the consensus horizon is parameterized by $D_0 = D - 1$ (`D_m1 : Nat`) so that $D = D_0 + 1$ is definitionally positive, and the block automaton and tree parity game solver are supplied via an arbitrary `Thm34Engine` instance `E`.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), Section 3.3, p. 15 (PDF 16), Lemma 3.12

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine
import Definitions.Def_DistLTLSynth_Char_SymbolicArena

set_option autoImplicit false

namespace DistLTLSynth.Char

theorem lemma_3_12 (E : Thm34Engine)
    (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ)
    (hparse : parse I.tokens = some φ)
    (hCons : ∀ g ∈ Pref c.lang, ConsensusSolvableWithin Bool (leftQuot g c.lang) (D_m1 + 1))
    (hlive0 : ([] : List CommGraph) ∈ Pref c.lang)
    (t0 : LabeledTree (NodeLabel I.X1 I.X2 I.Y1 I.Y2
      (Fin ((E.compileBlock (c, I, D_m1)).1.1 + 1))))
    (ht0 : IsUncompressedComponentTree
      (let D := D_m1 + 1
       let res := E.compileBlock (c, I, D_m1)
       let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
       ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩)
      {q | (E.compileBlock (c, I, D_m1)).2.getD q.val false = true} t0)
    (hacc0 : IsAcceptingTree
      (let D := D_m1 + 1
       let res := E.compileBlock (c, I, D_m1)
       let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
       ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩) t0) :
    let res := E.compileBlock (c, I, D_m1)
    let ctx : SymCtx := (I, D_m1, res.1, res.2)
    E.solveTreePG (buildTreeSpec E ctx) ≠ none := by sorry

end DistLTLSynth.Char
