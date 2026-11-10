-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_B_8
-- name    : FineGrainedEF.Main.lemma_B_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:09:42.313405+00:00
-- url     : https://prove2.me/theorems/a2ba65ab-a2c9-43d7-9dd5-9021694033e3
-- title:
--   Lemma B.8 — index-generalization: one derivation at an arbitrary index yields all m entrywise assertions at cost S + O(m(|P|+w+s+|z|))
-- statement:
--   Fix a number $c$ of arrays. Let $\Gamma$ be well formed, $A^{(1)},\dots,A^{(c)}$ arrays of wires of $\Gamma$, each of $m=2^s$ words of a common width at most $w$, $z$ a list of further wires, and $P$ a single-output check whose inputs are one word of each array, optionally an $s$-bit index, and $z$. For $j<m$ let $P_j$ be the copy of $P$ on $A^{(1)}_j,\dots,A^{(c)}_j$ (and the hardwired encoding of $j$) and $z$; for an $s$-bit index $i$ let $\varphi_i$ be the copy on $\mathrm{Sel}(A^{(1)},i),\dots,\mathrm{Sel}(A^{(c)},i)$ (and $i$) and $z$. There is one constant $K$ (depending only on $c$) such that, whenever
--   $$\Gamma'\ \triangleright^{S}_{\mathrm{EF}}\ \varphi_i=1\quad\text{for every well-formed }\Gamma'\supseteq\Gamma\text{ and every ordered tuple }i\text{ of }s\text{ wires of }\Gamma',$$
--   then
--   $$\Gamma\ \triangleright^{S+K\,m\,(|P|+w+s+|z|)}_{\mathrm{EF}}\ [P_j=1]_{j<m}.$$
--   Both universal quantifiers in the premise are essential (p. 11). Index-generalization is the paper's main new technique: a single derivation at a variable index replaces $m$ separate copies. Lemma 3.4 (p. 11) is its special case $c=1$ without index or extra wires.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: a fixed number c of arrays; cost S + O(m(|P|+w+s+|z|)) → ∀ c, ∃ K, then every context, array, check and S; cost S + K·2^s·(|P| + w + s + |z|); reason: c is fixed before the O-constant, as the lemma says; S is uniform over Γ′ and i in the premise
--   - encoding: P a single-output Boolean check of circuit size |P|; Γ′ ⊇ Γ → an abstract well-formed Circuit with one output, inputs ordered (array words, optional index, z); Γ′ ⊇ Γ keeps Γ's wires as a prefix; reason: input order fixes the interface; contexts are stored in introduction order, so adding declarations gives a prefix extension; arbitrary source extensions can be ordered with the old context first
--   - generalization: selectors on words of positive width (Section 3.1) → also permits zero-width array words and an empty list of arrays; reason: these contribute no input wires to P; positive-width source instances remain included with the same cost and quantifier order
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 60, Lemma B.8 (general form of Lemma 3.4, p. 11)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits

namespace FineGrainedEF.Main

/-- Lemma B.8 (Index-generalization, general form), p. 60. For every fixed number `c` of arrays
there is one constant `K` such that: for every well-formed `Γ`, every `s` (`m = 2^s`), every `w`
and `S`, all `c` arrays `A^(1), …, A^(c)` of `Γ`, each of `m` words of a common width at most `w`,
every list `z` of further wires of `Γ`, every flag saying whether the check reads an index, and
every well-formed single-output abstract check `P` whose inputs are one word of each array, then
(optionally) an `s`-bit index, then `z`: if for every well-formed context `Γ' ⊇ Γ` and every ordered
tuple `i` of `s` wires of `Γ'`, `Γ' ▷^S φ_i = 1` with `φ_i` the copy of `P` on
`Sel(A^(1), i), …, Sel(A^(c), i)` (and `i`), `z`, then `Γ ▷^{S + O(m(|P|+w+s+|z|))} [P_j = 1]_{j<m}`,
`P_j` the copy of `P` on `A^(1)_j, …, A^(c)_j` (and the hardwired `s`-bit encoding of `j`), `z`. -/
theorem lemma_B_8 :
    ∀ c : ℕ, ∃ K : ℕ, ∀ (Γ : Ctx) (s w S : ℕ) (A : List (List (List ℕ))) (useIdx : Bool)
      (z : List ℕ) (P : Circuit),
      Γ.WF → A.length = c →
      (∀ arr ∈ A, arr.length = 2 ^ s ∧ (arr.headD []).length ≤ w ∧
        ∀ x ∈ arr, x.length = (arr.headD []).length ∧ Γ.HasWires x) →
      Γ.HasWires z → P.WF → P.outs.length = 1 →
      P.nIn = (A.map fun arr => (arr.headD []).length).sum + (if useIdx then s else 0) + z.length →
      (∀ Γ' : Ctx, Γ'.WF → Γ'.Extends Γ → ∀ i : List ℕ, i.length = s → Γ'.HasWires i →
          BigStep Γ'
            (do let sels ← A.mapM fun arr => sel arr i
                P.apply (sels.flatten ++ (if useIdx then i else []) ++ z))
            S) →
      BigStep Γ
        ((List.range (2 ^ s)).mapM fun j => do
            let e ← if useIdx then encAddr s j else pure []
            let o ← P.apply ((A.map fun arr => arr.getD j []).flatten ++ e ++ z)
            pure (o.headD 0))
        (S + K * 2 ^ s * (P.size + w + s + z.length)) := by sorry

end FineGrainedEF.Main
