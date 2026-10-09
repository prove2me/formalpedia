-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_colWeight_le
-- name    : ExpanderBIS.Colorings.colWeight_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:27.928728+00:00
-- url     : https://prove2.me/theorems/9958d30d-fa2b-4e87-844c-9c0a7a94fab3
-- title:
--   §5.1, p. 31 — for γ ∈ 𝒞, w(γ) ≤ (1 − 1/q)^{|∂γ|} q^{|γ|} ≤ exp{−(Δ/(5q² log Δ))|γ|}
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $q \ge 3$, let $\Delta > Cq^2\log^2 q$, and let $G$ be a $\Delta$-regular bipartite graph with sides of size $m$ that is a $\bigl(\frac{4\log\Delta}{\Delta}, \frac{\Delta}{4\log\Delta} - \frac12\bigr)$-expander. Then for every pattern $(A,B)$ and every polymer $\gamma \in \mathcal C(G)$,
--   $$w_{A,B}(\gamma) \le \Bigl(1 - \frac1q\Bigr)^{|\partial\gamma|} q^{|\gamma|} \le \exp\Bigl\{-\frac{\Delta}{5q^2\log\Delta}|\gamma|\Bigr\}.$$
--
--   The weight of a polymer decays exponentially in its size, at a rate of order $\Delta/(q^2\log\Delta)$; this is the input to the Kotecký–Preiss estimate (15).
--
--   **Formalization Note.** For a pattern with an empty side the weight is $0$ under Lean's $x/0 = 0$, so the first inequality holds trivially there. Both inequalities are stated as a conjunction.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 31, §5.1, "w(γ) ≤ (1 − 1/q)^{|∂γ|} q^{|γ|} ≤ exp{−(Δ/(5q² log Δ))|γ|}"

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem colWeight_le :
    ∃ C : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ Δ : ℕ, C * (q : ℝ) ^ 2 * Real.log q ^ 2 < Δ →
      ∀ m : ℕ, ∀ G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ, ExpanderBIS.RandomHardCore.IsStdExpander G Δ →
        ∀ A : Finset (Fin q), ∀ γ ∈ colPolymers G q Δ,
          colWeight G q A γ ≤
              (1 - 1 / (q : ℝ)) ^ (ExpanderBIS.RandomHardCore.vertexBoundary G γ).card * (q : ℝ) ^ γ.card ∧
            (1 - 1 / (q : ℝ)) ^ (ExpanderBIS.RandomHardCore.vertexBoundary G γ).card * (q : ℝ) ^ γ.card ≤
              Real.exp (-((Δ : ℝ) / (5 * (q : ℝ) ^ 2 * Real.log Δ)) * γ.card) := by sorry

end ExpanderBIS.Colorings
