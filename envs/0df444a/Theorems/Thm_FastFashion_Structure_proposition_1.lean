-- Prove2me | Theorems.Thm_FastFashion_Structure_proposition_1
-- name    : FastFashion.Structure.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:35.843923+00:00
-- url     : https://prove2.me/theorems/3b5444e6-ac3f-410c-865f-6902c745aafa
-- title:
--   Proposition 1 — expected sales are non-decreasing, discretely concave in each variable, and supermodular
-- statement:
--   Let $\mathcal S = \mathcal S^+ \cup \mathcal S^-$ be a finite set of sizes split into major and minor sizes, let $(N_s)_{s \in \mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$ on a probability space, let $T > 0$ be the time between replenishments, and let $g(q) = \mathbb E[G(q)]$ be the expected sales of equation (1) as a function of the inventory vector $q \in \mathbb N^{\mathcal S}$. Write $\Delta_s g(q) = g(q + e_s) - g(q)$. Then
--   1. $g$ is non-decreasing: $q \le q'$ componentwise implies $g(q) \le g(q')$;
--   2. $g$ is discretely concave in each variable: $\Delta_s g(q + e_s) \le \Delta_s g(q)$ for all $q$ and $s$;
--   3. the marginal differences are non-decreasing in the other variables: $\Delta_s g(q) \le \Delta_s g(q + e_{s'})$ for all $q$ and all $s \ne s'$;
--   4. $g$ is supermodular on the lattice $\mathbb N^{\mathcal S}$:
--   $$g(q) + g(q') \le g(q \vee q') + g(q \wedge q') \qquad \text{for all } q, q' \in \mathbb N^{\mathcal S}.$$
--
--   The proposition shows that the sales model captures the two qualitative features the inventory allocation needs: decreasing marginal returns to shipping more of a size to a store, and complementarity across sizes induced by the policy of removing a garment from display when a major size runs out.
--
--   **Formalization Note** The paper writes "non-decreasing in $x_s$", a typo for $q_s$. Items 2 and 3 are the paper's "That is" reading; item 4 is the word "supermodular" in Topkis's lattice sense (the published platform definition `SupermodularOn` on the whole lattice). Both are stated because the paper states both. No hypothesis is placed on the set of major sizes; for $\mathcal S^+ = \emptyset$ the first sum in (1) is empty and $\tau_{\mathcal S^+} = +\infty$.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 11, Proposition 1; proof pp. 30–31, Appendix §5.1

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace FastFashion.Structure

open MeasureTheory ProbabilityTheory

theorem proposition_1 {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (Sp : Finset S) :
    Monotone (expectedSales N P Sp T) ∧
    (∀ (q : S → ℕ) (s : S),
      delta (expectedSales N P Sp T) s (q + Pi.single s 1)
        ≤ delta (expectedSales N P Sp T) s q) ∧
    (∀ (q : S → ℕ) (s s' : S), s ≠ s' →
      delta (expectedSales N P Sp T) s q
        ≤ delta (expectedSales N P Sp T) s (q + Pi.single s' 1)) ∧
    Supermodularity.Monotonicity.SupermodularOn (expectedSales N P Sp T) Set.univ := by sorry

end FastFashion.Structure
