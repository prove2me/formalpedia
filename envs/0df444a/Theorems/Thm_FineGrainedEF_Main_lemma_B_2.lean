-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_B_2
-- name    : FineGrainedEF.Main.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:09:40.48636+00:00
-- url     : https://prove2.me/theorems/d43fbcad-c15d-40b7-ae6e-01d5954834fc
-- title:
--   Lemma B.2 — folding: asserted leaves give the AND-tree (negated OR-tree) assertion at cost O(m), with conditional forms
-- statement:
--   Let $\Gamma$ be a well-formed context, $P_0,\dots,P_{m-1}$ ($m\ge1$) wires of $\Gamma$ and $H$ a wire of $\Gamma$ ($H$ need not be asserted). There is one constant $C$ such that, for all such data, with premises and their check circuits supplied in $\Gamma$,
--   $$\Gamma:[P_j]_{j<m}\ \triangleright^{Cm}_{\mathrm{EF}}\ \bigwedge_{j<m}P_j,\qquad \Gamma:[H\to P_j]_{j<m}\ \triangleright^{Cm}_{\mathrm{EF}}\ H\to\bigwedge_{j<m}P_j,$$
--   $$\Gamma:[\neg P_j]_{j<m}\ \triangleright^{Cm}_{\mathrm{EF}}\ \neg\Big(\bigvee_{j<m}P_j\Big),\qquad \Gamma:[H\to\neg P_j]_{j<m}\ \triangleright^{Cm}_{\mathrm{EF}}\ H\to\neg\Big(\bigvee_{j<m}P_j\Big).$$
--   The tree and its top gates are the conclusion circuit (not charged). Folding is the basic way to combine many assertions into one checked wire; it is used throughout Appendices B–J.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - generalization: ⋀_{j<m}, ⋁_{j<m} balanced trees for m a power of two, m ≥ 2 (p. 9) → every m ≥ 1, balanced tree split at ⌈m/2⌉ (m = 1: the leaf itself); reason: the source explicitly fixes power-of-two trees with m ≥ 2; the Lean also covers every nonempty balanced tree, including one leaf, and specializes to the entire source family; floor(log₂ m)+1 and log₂ m are within a constant factor on m ≥ 2
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 55, Lemma B.2 (47)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits

namespace FineGrainedEF.Main

/-- Lemma B.2 (Folding Boolean assertions), p. 55. One constant `C` for the whole family: every
well-formed context `Γ`, every list of `m ≥ 1` leaf wires `P_0, …, P_{m-1}` of `Γ` and every wire
`H` of `Γ`. Premises are supplied in `Γ` (their check circuits included); the conclusion circuit
(the tree and its top gates) is the expanded context and is not charged.
(i) `Γ : [P_j]_{j<m} ▷^{O(m)} ⋀_{j<m} P_j` (47);
(ii) `Γ : [H → P_j]_{j<m} ▷^{O(m)} H → ⋀_{j<m} P_j`;
(iii) `Γ : [¬P_j]_{j<m} ▷^{O(m)} ¬(⋁_{j<m} P_j)`;
(iv) `Γ : [H → ¬P_j]_{j<m} ▷^{O(m)} H → ¬(⋁_{j<m} P_j)`. -/
theorem lemma_B_2 :
    ∃ C : ℕ, ∀ (Γ : Ctx) (H : ℕ) (P : List ℕ), Γ.WF → 1 ≤ P.length → Γ.HasWires (H :: P) →
      ((∀ p ∈ P, p ∈ Γ.asserted) →
          BigStep Γ (do let t ← andTree P; pure [t]) (C * P.length)) ∧
      ((∀ p ∈ P, Asserts Γ (impG H p)) →
          BigStep Γ (do let t ← andTree P; let h ← impG H t; pure [h]) (C * P.length)) ∧
      ((∀ p ∈ P, Asserts Γ (notG p)) →
          BigStep Γ (do let t ← orTree P; let nt ← notG t; pure [nt]) (C * P.length)) ∧
      ((∀ p ∈ P, Asserts Γ (do let np ← notG p; impG H np)) →
          BigStep Γ (do let t ← orTree P; let nt ← notG t; let h ← impG H nt; pure [h])
            (C * P.length)) := by sorry

end FineGrainedEF.Main
