-- Prove2me | Theorems.Thm_Finset_graph_balogSzemerediGowers_restricted_sumset_explicit
-- name    : Finset.graph_balogSzemerediGowers_restricted_sumset_explicit
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:07.800115+00:00
-- url     : https://prove2.me/theorems/26588a82-0360-42ec-83aa-be39b112b0bf
-- title:
--   Graph BSG with explicit bounds $\delta/8$ and $2^{13}K^3/\delta^5 + 2^{12}/\delta^5$
-- statement:
--   Let $G$ be an additive commutative group, $\delta > 0$, $K > 0$, and $A, B \subseteq G$ nonempty finite sets with $|A| = |B|$. Let $E \subseteq A \times B$ satisfy $$|E| \ge \delta\,|A|^2, \qquad |\{a + b : (a,b) \in E\}| \le K\,|A|.$$ Then there exist $A' \subseteq A$ and $B' \subseteq B$ with $$|A'| \ge \tfrac{\delta}{8}\,|A|, \qquad |B'| \ge \tfrac{\delta}{8}\,|A|$$ and $$|A' + B'| \le \left(\tfrac{2^{13} K^3}{\delta^5} + \tfrac{2^{12}}{\delta^5}\right) |A|.$$ This is the quantitative graph Balog–Szemerédi–Gowers theorem with all constants tracked: the surviving density is $\delta/8$ and the sumset blow-up is polynomial in $K$ and $\delta^{-1}$. Its proof combines degree regularization, dependent random choice (producing a $3$-path-rich rectangle), the Tao–Vu triple-count injection, and double counting; it is the engine that, applied to the popular-sum graph, gives the explicit asymmetric BSG bound.
-- source:
--   Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Section 5.1 (p. 9) / Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Theorem 2.29 (p. 79), with explicit constants. The formalized bound 2^13 K^3/delta^5 + 2^12/delta^5 is slightly weaker than the source's 2^12 C^3 c^-5; the extra additive term absorbs the small-cardinality edge case. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2230-L2430

import Mathlib

open scoped Pointwise

theorem Finset.graph_balogSzemerediGowers_restricted_sumset_explicit {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (A B : Finset G) (hA : A.Nonempty) (_hB : B.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_lb : δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ))
    (hS_ub : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (A.card : ℝ) := by sorry
