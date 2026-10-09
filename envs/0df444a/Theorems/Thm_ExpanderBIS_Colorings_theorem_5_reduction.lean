-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_theorem_5_reduction
-- name    : ExpanderBIS.Colorings.theorem_5_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:09.448535+00:00
-- url     : https://prove2.me/theorems/ead289ee-8b0d-436f-b42b-4d6d0d2f7734
-- title:
--   Theorem 5 (core) — for Δ ≥ Cq² log² q, almost every Δ-regular bipartite graph has Z̃_G(q) ≈ Z_G(q) within e^{−m/(4q)} and Kotecký–Preiss for every pattern
-- statement:
--   There is an absolute constant $C > 0$ such that for every $q \ge 3$ and every $\Delta \ge Cq^2\log^2 q$, almost every $\Delta$-regular bipartite graph $G$ (with sides of size $m$, $m \to \infty$) has both of the following properties.
--
--   1. The polymer approximant $\tilde Z_G(q) = \sum_{(A,B)} |A|^m|B|^m\,\Xi_{A,B}(G)$ is an $e^{-m/(4q)}$-relative approximation to the number $Z_G(q)$ of proper $q$-colorings of $G$.
--   2. For every pattern $(A,B)$, the polymer model $(\mathcal C(G), w_{A,B})$ satisfies the Kotecký–Preiss condition with decay function $g(\gamma) = \frac{\Delta}{10q^2\log\Delta}|\gamma|$: for every polymer $\gamma \in \mathcal C(G)$,
--   $$\sum_{\gamma' \in \mathcal C(G):\ d(\gamma',\gamma) \le 3} w_{A,B}(\gamma')\, e^{|\gamma'| + g(\gamma')} \le |\gamma|.$$
--
--   Here $d(\gamma',\gamma) \le 3$ means that $\gamma'$ is incompatible with $\gamma$ (some vertex of $\gamma'$ is within $G$-distance $3$ of some vertex of $\gamma$), which includes $\gamma' = \gamma$.
--
--   This is the mathematical content of Theorem 5: the paper turns properties 1 and 2 into an FPTAS and a polynomial-time sampler for proper $q$-colorings via a cluster-expansion algorithm (its Theorem 8, adapted from Helmuth, Perkins and Regts). The algorithm and its running time are not part of this statement.
--
--   **Formalization Note.** "Almost every" is the limit, as $m \to \infty$, of the fraction of labelled $\Delta$-regular bipartite graphs on two fixed sides of size $m$ that satisfy both properties; the fixed-sides model is a disclosed choice. $C$ is quantified before $q$ and $\Delta$. The pattern quantifier sits inside the almost-every event, as in the paper.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 5, Theorem 5 (proof §5, pp. 26–32; Lemma 29, p. 27; Kotecký–Preiss condition, p. 30; §5.2, p. 31)

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem theorem_5_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 3 ≤ q → ∀ Δ : ℕ, C * (q : ℝ) ^ 2 * Real.log q ^ 2 ≤ Δ →
      ExpanderBIS.RandomHardCore.AlmostEvery Δ (fun m G =>
        ExpanderBIS.Potts.IsRelApprox (Real.exp (-((m : ℝ) / (4 * q)))) (Ztilde G q Δ)
            ((properColorings G q).card) ∧
          ∀ A : Finset (Fin q), ∀ γ ∈ colPolymers G q Δ,
            ∑ γ' ∈ (colPolymers G q Δ).filter (fun γ' => ¬ Compat3 G γ' γ),
                colWeight G q A γ' * Real.exp (γ'.card + colDecay q Δ γ') ≤ γ.card) := by sorry

end ExpanderBIS.Colorings
