-- Prove2me | Theorems.Thm_Finset_graph_balogSzemerediGowers_restricted_sumset
-- name    : Finset.graph_balogSzemerediGowers_restricted_sumset
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:03.720626+00:00
-- url     : https://prove2.me/theorems/a15c7424-e6e8-4470-9455-a6838e21bdcc
-- title:
--   Graph Balog–Szemerédi–Gowers theorem (qualitative)
-- statement:
--   Let $G$ be an arbitrary additive commutative group. For every $\delta > 0$ and $K > 0$ there exist $c > 0$ and $C > 0$ (depending only on $\delta, K$) such that the following holds. Let $A, B \subseteq G$ be nonempty finite sets with $|A| = |B|$ and let $E \subseteq A \times B$ satisfy the density and restricted-sumset bounds $$|E| \ge \delta\,|A|^2, \qquad |\{a + b : (a,b) \in E\}| \le K\,|A|.$$ Then there exist $A' \subseteq A$ and $B' \subseteq B$ with $$|A'| \ge c\,|A|, \qquad |B'| \ge c\,|A|, \qquad |A' + B'| \le C\,|A|.$$ This is the qualitative graph (Balog–Szemerédi–Gowers) step: a dense bipartite graph with small restricted sumset contains large vertex subsets spanning an honestly small sumset. It is the bridge of the whole proof — the popular-sum graph produced from large energy satisfies exactly its hypotheses, and its conclusion plus Ruzsa calculus yields the ordinary asymmetric BSG theorem.
-- source:
--   Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Section 5.1, the displayed bound |A'+B'| <= 2^12 C^3 c^-5 n (p. 9); the same theorem is Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Theorem 2.29 (p. 79). Qualitative form, constants left existential. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L1972-L2227

import Mathlib

open scoped Pointwise

theorem Finset.graph_balogSzemerediGowers_restricted_sumset {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ δ K : ℝ, 0 < δ → 0 < K → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A B : Finset G, A.Nonempty → B.Nonempty → A.card = B.card →
        ∀ E : Finset (G × G), E ⊆ A ×ˢ B →
          δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ) →
          ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ) →
          ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
            c * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            c * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
            ((A' + B').card : ℝ) ≤ C * (A.card : ℝ) := by sorry
