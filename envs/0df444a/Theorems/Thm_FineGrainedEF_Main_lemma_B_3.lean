-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_B_3
-- name    : FineGrainedEF.Main.lemma_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:09:38.952436+00:00
-- url     : https://prove2.me/theorems/a2a5eb62-13e3-4a5c-ad21-de0f1e3f5102
-- title:
--   Lemma B.3 — unfolding: an asserted AND-tree (negated OR-tree) gives all leaves at cost O(m) or one leaf at cost O(log m)
-- statement:
--   Let $\Gamma$ be well formed and contain the gate definitions of the balanced tree $\bigwedge_{j<m}P_j$ (resp. $\bigvee_{j<m}P_j$) with output $t$, $m\ge1$, and let $H$ be a wire. There is one constant $C$ such that for every such $\Gamma$ and every fixed leaf $j<m$:
--   $$\Gamma:\bigwedge_{j<m}P_j\ \triangleright^{Cm}\ [P_j]_{j<m}\ \ (48),\qquad \Gamma:\bigwedge_{j<m}P_j\ \triangleright^{C(\lfloor\log_2m\rfloor+1)}\ P_j\ \ (49),$$
--   $$\Gamma:H\to\bigwedge_{j<m}P_j\ \triangleright^{Cm}\ [H\to P_j]_{j<m},\qquad \Gamma:H\to\bigwedge_{j<m}P_j\ \triangleright^{C(\lfloor\log_2m\rfloor+1)}\ H\to P_j,$$
--   and the same four rules for the OR tree with $\neg(\bigvee_{j<m}P_j)$ as premise and $\neg P_j$ (resp. $H\to\neg P_j$) as conclusions. Unfolding inverts folding and is how a single checked conjunction is turned back into its coordinate assertions.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - generalization: ⋀, ⋁ over m = 2^s ≥ 2 leaves; cost O(log m) → every m ≥ 1 with the pinned balanced tree; O(log m) as C·(⌊log₂ m⌋ + 1); reason: the source explicitly fixes power-of-two trees with m ≥ 2; the Lean also covers every nonempty balanced tree, including one leaf, and specializes to the entire source family; floor(log₂ m)+1 and log₂ m are within a constant factor on m ≥ 2
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 55-56, Lemma B.3 (48)-(49)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits

namespace FineGrainedEF.Main

/-- Lemma B.3 (Unfolding a Boolean tree), pp. 55–56. One constant `C` for the whole family: every
well-formed `Γ`, every list of `m ≥ 1` leaf wires `P_j` of `Γ`, every wire `H`, every tree output
`t` of a copy of the tree contained in `Γ`, and every fixed leaf address `j < m`. `O(m)` is
`C·m`; `O(log m)` is `C·(⌊log₂ m⌋ + 1)`. The eight rules:
AND tree, `Γ : ⋀ P_j ▷^{O(m)} [P_j]_{j<m}` (48) and `▷^{O(log m)} P_j` (49);
conditional, `Γ : H → ⋀ P_j ▷^{O(m)} [H → P_j]_{j<m}` and `▷^{O(log m)} H → P_j`;
OR tree, `Γ : ¬(⋁ P_j) ▷^{O(m)} [¬P_j]_{j<m}` and `▷^{O(log m)} ¬P_j`;
conditional, `Γ : H → ¬(⋁ P_j) ▷^{O(m)} [H → ¬P_j]_{j<m}` and `▷^{O(log m)} H → ¬P_j`. -/
theorem lemma_B_3 :
    ∃ C : ℕ, ∀ (Γ : Ctx) (H t : ℕ) (P : List ℕ), Γ.WF → 1 ≤ P.length → Γ.HasWires (H :: P) →
      (Contains Γ (andTree P) t → t ∈ Γ.asserted →
          BigStep Γ (pure P) (C * P.length) ∧
          ∀ j < P.length, BigStep Γ (pure [P.getD j 0]) (C * (Nat.log 2 P.length + 1))) ∧
      (Contains Γ (andTree P) t → Asserts Γ (impG H t) →
          BigStep Γ (P.mapM fun p => impG H p) (C * P.length) ∧
          ∀ j < P.length, BigStep Γ (do let h ← impG H (P.getD j 0); pure [h])
            (C * (Nat.log 2 P.length + 1))) ∧
      (Contains Γ (orTree P) t → Asserts Γ (notG t) →
          BigStep Γ (P.mapM fun p => notG p) (C * P.length) ∧
          ∀ j < P.length, BigStep Γ (do let np ← notG (P.getD j 0); pure [np])
            (C * (Nat.log 2 P.length + 1))) ∧
      (Contains Γ (orTree P) t → Asserts Γ (do let nt ← notG t; impG H nt) →
          BigStep Γ (P.mapM fun p => do let np ← notG p; impG H np) (C * P.length) ∧
          ∀ j < P.length, BigStep Γ (do let np ← notG (P.getD j 0); let h ← impG H np; pure [h])
            (C * (Nat.log 2 P.length + 1))) := by sorry

end FineGrainedEF.Main
