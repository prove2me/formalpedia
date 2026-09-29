-- Prove2me | Theorems.Thm_Finset_path3_count_le_triple_rep_count
-- name    : Finset.path3_count_le_triple_rep_count
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:10.255499+00:00
-- url     : https://prove2.me/theorems/c9ef21c1-349d-498f-8818-c9f667034f98
-- title:
--   Tao–Vu $3$-path count bounded by $s_1 - s_2 + s_3$ triples
-- statement:
--   Let $G$ be an additive commutative group, $A, B, S \subseteq G$ finite sets, and $E \subseteq G \times G$ a set of pairs all of whose sums lie in $S$ (i.e. $(x,y) \in E \Rightarrow x + y \in S$). For fixed endpoints $a, b \in G$, the number of length-$3$ paths $$a \to b_1 \to a_2 \to b, \qquad (b_1, a_2) \in B \times A,\ (a,b_1),(a_2,b_1),(a_2,b) \in E$$ satisfies $$\#\{\text{$3$-paths from $a$ to $b$ through $E$}\} \le \#\{(s_1, s_2, s_3) \in S^3 : s_1 - s_2 + s_3 = a + b\}.$$ The map $(b_1, a_2) \mapsto (a + b_1,\, a_2 + b_1,\, a_2 + b)$ is injective with the relation $s_1 - s_2 + s_3 = a + b$. This Tao–Vu injection is the key algebraic step of the graph BSG proof: path richness of a pair $(a,b)$ forces the triple-representation number of $a + b$ from the small set $S$ to be large, so a uniform path lower bound over $A' \times B'$ yields, by double counting, the bound $|A' + B'| \le |S|^3 / M$.
-- source:
--   Injection step y = x - x' + x'' inside Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Section 5.1 (p. 9) / the proof of Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Theorem 2.29. Not separately stated in the cited works. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L441-L502

import Mathlib

open scoped Pointwise

theorem Finset.path3_count_le_triple_rep_count {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (E : Finset (G × G)) (hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S)
    (a b : G) :
    (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
    ≤ ((S ×ˢ S ×ˢ S).filter
        fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card := by sorry
