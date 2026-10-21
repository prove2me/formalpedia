-- Prove2me | Theorems.Thm_CoProdBundle_Equil_lemma_1
-- name    : CoProdBundle.Equil.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:34.439123+00:00
-- url     : https://prove2.me/theorems/6db0478d-4c97-4e68-8125-8024d9d049d8
-- title:
--   Lemma 1, p. 14 — the unique equilibrium: K = max{i : c_i ≤ (c_1+…+c_i)/(i − (1−3θ/2))}, Q*_i (2b), Q* (2c), P*(Q) = (2A+bc)Q^θ/(3b)
-- statement:
--   **Lemma 1 (Equilibrium Solution).** Consider $I \ge 1$ producers with unit costs $0 < c_1 \le c_2 \le \dots \le c_I$, demand $D(P,Q) = \sqrt{AQ^\theta - bP}$ with $b > 0$ and $0 < \theta < 2/3$, distribution cost $wQ^\theta$ with $A - bw > 0$, and revenue share $0 < \gamma < 1$ for the producers. Each producer $i$ chooses $Q_i \ge 0$ and earns $\gamma (Q_i/Q) S(Q) - c_iQ_i$, where $Q = \sum_j Q_j$ and $S(Q)$ is the surplus at the retailer's optimal price. Write $\alpha = 1 - 3\theta/2$ and let
--   $$K = \max\Bigl\{i : c_i \le \frac{c_1 + \dots + c_i}{i - (1 - 3\theta/2)}\Bigr\}, \qquad (2a)$$
--   $$Q^* = \Bigl[\frac{2\gamma}{b}\,\frac{K - \alpha}{c_1 + \dots + c_K}\Bigr]^{2/(2-3\theta)}\Bigl(\frac{A - bw}{3}\Bigr)^{3/(2-3\theta)}, \qquad (2c)$$
--   $$Q^*_i = \Bigl[1 - c_i\,\frac{K - \alpha}{c_1 + \dots + c_K}\Bigr]\frac{2Q^*}{2 - 3\theta}\ \ (i \le K), \qquad Q^*_i = 0\ \ (i > K). \qquad (2b)$$
--   Then:
--   1. $1 \le K \le I$;
--   2. for every $Q > 0$ the retailer's optimal price is unique and equals $P^*(Q) = \dfrac{2A + bw}{3b}\,Q^\theta$ (2d);
--   3. a profile of outputs is a Nash equilibrium of the producers' game **if and only if** it is $(Q^*_1, \dots, Q^*_I)$;
--   4. $\sum_i Q^*_i = Q^*$;
--   5. every $Q^*_i \ge 0$;
--   6. $Q^*_i > 0$ exactly when $i \le K$ and $c_i < (c_1 + \dots + c_K)/(K - \alpha)$;
--   7. if $K = 1$, then $Q^*_1 = Q^* = \Bigl(\dfrac{3\gamma\theta}{bc_1}\Bigr)^{2/(2-3\theta)}\Bigl(\dfrac{A-bw}{3}\Bigr)^{3/(2-3\theta)}$;
--   8. if there are at least two producers, $K = 1$ if and only if $c_2 > 2c_1/(3\theta)$.
--
--   The lemma solves the co-produced bundle economy in closed form. The results of the rest of the paper (how outputs, participation and total value respond to costs, revenue share and bundle elasticity) are derived from these formulas.
--
--   **Formalization Note** "The equilibrium" is read as the unique Nash equilibrium (item 3). With the weak inequality of (2a), a producer $i \le K$ whose cost equals $(c_1+\dots+c_K)/(K-\alpha)$ has $Q^*_i = 0$ by (2b); item 6 states exactly which producers have positive output. The paper's distribution-cost coefficient $c$ is `w`; Lean's producer `⟨0, hI⟩` is the paper's producer 1, `⟨1, h⟩` producer 2. The standing assumptions $c_i > 0$, $b > 0$, $A - bw > 0$ are implicit in the paper and needed for the formulas to make sense; $\gamma < 1$ makes the retailer's price unique.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), Lemma 1, (2a)–(2d), p. 14

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- Lemma 1 (Equilibrium Solution), p. 14. -/
theorem lemma_1 (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (1 ≤ Kstar c θ ∧ Kstar c θ ≤ I) ∧
    (∀ Q : ℝ, 0 < Q → IsRetailerOptimal γ A b w θ Q (Pstar A b w θ Q) ∧
      ∀ P : ℝ, IsRetailerOptimal γ A b w θ Q P → P = Pstar A b w θ Q) ∧
    (∀ q : Fin I → ℝ, IsNashEq γ A b w θ c q ↔ q = qstar γ A b w θ c) ∧
    total (qstar γ A b w θ c) = Qstar γ A b w θ c ∧
    (∀ i, 0 ≤ qstar γ A b w θ c i) ∧
    (∀ i, 0 < qstar γ A b w θ c i ↔
      ((i : ℕ) < Kstar c θ ∧ c i < psum c (Kstar c θ) / ((Kstar c θ : ℝ) - alpha θ))) ∧
    (Kstar c θ = 1 → qstar γ A b w θ c ⟨0, hI⟩ =
      (3 * γ * θ / (b * c ⟨0, hI⟩)) ^ (2 / (2 - 3 * θ)) * ((A - b * w) / 3) ^ (3 / (2 - 3 * θ))) ∧
    (∀ h : 1 < I, Kstar c θ = 1 ↔ 2 * c ⟨0, hI⟩ / (3 * θ) < c ⟨1, h⟩) := by sorry

end CoProdBundle.Equil
