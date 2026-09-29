-- Prove2me | Theorems.Thm_Finset_balog_szemeredi_gowers_asymmetric
-- name    : Finset.balog_szemeredi_gowers_asymmetric
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:07.432024+00:00
-- url     : https://prove2.me/theorems/e884880d-be8f-4491-8716-b299166034f3
-- title:
--   Asymmetric Balog–Szemerédi–Gowers theorem (qualitative)
-- statement:
--   Let $G$ be an arbitrary additive commutative group and $\eta > 0$. There exist constants $c > 0$ and $C > 0$, depending only on $\eta$, such that the following holds. Let $X, Y \subseteq G$ be nonempty finite sets with $|X| = |Y|$ whose additive energy satisfies
--   $$E(X, Y) \ge \eta\, |X|^3.$$
--   Then there exist subsets $X' \subseteq X$ and $Y' \subseteq Y$ with
--   $$|X'| \ge c\,|X|, \qquad |Y'| \ge c\,|Y|, \qquad |X' - Y'| \le C\,|X|.$$
--   Here $E(X,Y)$ counts the additive quadruples $x_1 + y_1 = x_2 + y_2$ with $x_i \in X$ and $y_i \in Y$, and $X' - Y' = \{x - y : x \in X', y \in Y'\}$ is the pointwise difference set. The cardinality bounds $c|X| \le |X'|$ and $c|Y| \le |Y'|$ already force $X'$ and $Y'$ to be nonempty, so no separate nonemptiness clause is needed.
--
--   This is the qualitative asymmetric form of the Balog-Szemeredi-Gowers theorem: large additive energy forces large subsets whose difference set is linear in $|X|$. The conclusion bounds the difference set $|X' - Y'|$, and this is not a restatement of a sumset bound. The graph step of the proof delivers a bound on the sumset, $|X' + Y'| \le C_0|X|$; converting that into the difference-set bound is a separate Ruzsa argument (`Finset.ruzsa_sumset_to_difference`) which costs a factor, replacing the sumset constant $C_0/c_0$ by $(C_0/c_0)^3/c_0 + 1$.
--
--   It is the top-level asymmetric conclusion of the project, deduced from the popular-sum graph construction, the graph (restricted-sumset) Balog-Szemeredi-Gowers theorem, and that Ruzsa conversion.
-- source:
--   Asymmetric Balog-Szemeredi-Gowers over additive energy (Balog-Szemeredi 1994; Gowers 1998). This exact statement is not stated in any cited work: it is assembled from Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Lemma 2.30 (energy to graph, p. 80), Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99 Section 5.1 / Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006) Theorem 2.29 (graph bound, p. 79), and Ruzsa calculus to pass from the sumset bound to the difference-set conclusion. Constants left existential. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2432-L2651

import Mathlib

open scoped Pointwise

theorem Finset.balog_szemeredi_gowers_asymmetric {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ X Y : Finset G, X.Nonempty → Y.Nonempty → X.card = Y.card →
        η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ) →
        ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
          c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          c * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
          ((X' - Y').card : ℝ) ≤ C * (X.card : ℝ) := by sorry
