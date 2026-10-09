-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_eq_15
-- name    : ExpanderBIS.Colorings.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:56.605912+00:00
-- url     : https://prove2.me/theorems/d2d6cb47-16c7-4ebc-b1a4-6a3d22e4f6ee
-- title:
--   (15), p. 31 — Σ_{γ′ ∋ v} w(γ′) e^{|γ′| + g(γ′)} ≤ 1/Δ³ for every vertex v
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $q \ge 3$, let $\Delta > Cq^2\log^2 q$, and let $G$ be a $\Delta$-regular bipartite graph with sides of size $m$ that is a $\bigl(\frac{4\log\Delta}{\Delta}, \frac{\Delta}{4\log\Delta} - \frac12\bigr)$-expander. Then for every pattern $(A,B)$ and every vertex $v$,
--   $$\sum_{\gamma' \in \mathcal C(G),\ \gamma' \ni v} w_{A,B}(\gamma')\, e^{|\gamma'| + g(\gamma')} \le \frac{1}{\Delta^3}, \qquad g(\gamma) = \frac{\Delta}{10q^2\log\Delta}|\gamma|.$$
--
--   Summed over the at most $\Delta^3|\gamma|$ vertices within distance $3$ of a polymer $\gamma$, this gives the Kotecký–Preiss condition for the polymer model of every pattern.
--
--   **Formalization Note.** Only the two ends of the printed chain (15) are stated; the middle series $\sum_{t\ge1}(e^2\Delta^3)^t\exp\{-\frac{\Delta}{10q^2\log\Delta}t\}$ belongs to the proof.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 31, (15)

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem eq_15 :
    ∃ C : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ Δ : ℕ, C * (q : ℝ) ^ 2 * Real.log q ^ 2 < Δ →
      ∀ m : ℕ, ∀ G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ, ExpanderBIS.RandomHardCore.IsStdExpander G Δ →
        ∀ A : Finset (Fin q), ∀ v : ExpanderBIS.RandomHardCore.Vertex m,
          ∑ γ' ∈ (colPolymers G q Δ).filter (fun γ' => v ∈ γ'),
              colWeight G q A γ' * Real.exp (γ'.card + colDecay q Δ γ') ≤
            1 / (Δ : ℝ) ^ 3 := by sorry

end ExpanderBIS.Colorings
