-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_9
-- name    : DistLTLSynth.Char.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:17:45.527556+00:00
-- url     : https://prove2.me/theorems/cdb9908f-9686-4a8c-8a22-233aff48b45a
-- title:
--   Lemma 3.9 — realizing algorithms correspond to accepting uncompressed component trees; effective extraction
-- statement:
--   Let $D\ge1$ and let $B$ (a deterministic parity automaton over blocks $\Sigma^D\times\Omega^D$ with finitely many states) and $Q_{\mathrm{live}}$ satisfy the conclusion of Lemma 3.7 for $A$ and $\varphi$. Then
--
--   1. a distributed algorithm realizing $\varphi$ under $A$ exists **if and only if** an accepting uncompressed component tree exists;
--   2. from an effectively given accepting uncompressed tree one can compute the local output functions of a realizing algorithm: there is a computable map $F$ on codes such that, whenever $c$ effectively gives an accepting uncompressed component tree, $F(c)$ computes $f_1,f_2$ of an algorithm realizing $\varphi$ under $A$.
--
--   It turns synthesis into a question about trees with finitely many labels per node.
--
--   Differences from the source:
--   - generalization: D is the uniform consensus bound of Lemma 3.6 and B, Q_live are the block automaton built in the proof of Lemma 3.7 from A_live and A_ϕ, for an ω-regular A with nowhere-dense image → any D ≥ 1, any finite deterministic parity automaton B over blocks and any Q_live satisfying the two properties of Lemma 3.7, for any A; reason: the correspondence uses only those two properties and D ≥ 1, not the consensus property; the paper's D, B, Q_live are an instance
--   - encoding: edges {v_1(h), v_2(h)} of view complexes; positions (K, q) and output labelings λ → edges as their histories h; labels as finite lists of (edge, state) and (view, output) pairs read by first match; reason: the paper notes that the pair of views determines the history; finite lists make labels encodable
--   - encoding: 'one can compute the local output functions' from an effectively given tree → a computable F : Nat.Partrec.Code → Nat.Partrec.Code mapping every code effectively giving an accepting tree to a code computing (f_1, f_2); reason: the uniform reading of 'from … one can compute'
--   - encoding: finite nonempty X_p, Y_p → Fintype + Nonempty/Inhabited with Encodable and DecidableEq instances; reason: every finite type has them; computability does not depend on the choice of encoding of a finite type
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
--   - encoding: a rooted tree whose children are the connected components of K^(D)_live → LabeledTree: a label and a number of children at each address (list of child numbers), nodes the valid addresses; reason: K is finite and Σ^D is finite, so K^(D)_live has finitely many components and every uncompressed component tree is finitely branching; this is the child numbering that 'effectively given' (p. 13) uses
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 13 (PDF 14), Lemma 3.9 (Definition 3.8 and 'effectively given', p. 13)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree

namespace DistLTLSynth.Char

/-- Lemma 3.9: (for a block length `D ≥ 1` and a block automaton `B` with `Q_live` as in
Lemma 3.7) a distributed algorithm realizing `ϕ` under `A` exists iff an accepting
uncompressed component tree exists; and from an effectively given accepting uncompressed
tree one can compute the local output functions of a realizing algorithm. -/
theorem lemma_3_9 {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Nonempty X1] [DecidableEq X1]
    [Encodable X1] [Fintype X2] [Nonempty X2] [DecidableEq X2] [Encodable X2]
    [Fintype Y1] [Inhabited Y1] [Encodable Y1] [Fintype Y2] [Inhabited Y2] [Encodable Y2]
    [Fintype QB] [Encodable QB]
    (A : Set (ℕ → CommGraph)) (φ : Formula X1 X2 Y1 Y2) (D : ℕ) (hD : 1 ≤ D)
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (hB : IsBlockAutomaton A φ D B Qlive) :
    ((∃ f : Algorithm X1 X2 Y1 Y2, FRealizes f A φ) ↔
        ∃ t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB),
          IsUncompressedComponentTree B Qlive t ∧ IsAcceptingTree B t) ∧
      ∃ F : Nat.Partrec.Code → Nat.Partrec.Code, Computable F ∧
        ∀ (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) (c : Nat.Partrec.Code),
          IsUncompressedComponentTree B Qlive t → IsAcceptingTree B t → EffectivelyGiven t c →
            ∃ f : Algorithm X1 X2 Y1 Y2, CodeComputes (F c) f ∧ FRealizes f A φ := by sorry

end DistLTLSynth.Char
