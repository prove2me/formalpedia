-- Prove2me | Theorems.Thm_DualSSD_MeanRisk_meanGini_optimal_exists_ssdEfficient
-- name    : DualSSD.MeanRisk.meanGini_optimal_exists_ssdEfficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:08:35.087953+00:00
-- url     : https://prove2.me/theorems/2ef72def-4629-453d-838f-37bd00b85444
-- title:
--   Theorem 5.3 — mean–Gini optimal solutions exist and are SSD-efficient
-- statement:
--   Let $1<q<\infty$ and let $Q\subseteq L_q(\Omega,P)$ be a nonempty, convex, bounded and closed set. Consider the mean–risk problem with the Gini mean difference as risk functional,
--
--   $$\max_{X\in Q}\ (\mu_X-\lambda\Gamma_X).\tag{5.1}$$
--
--   Then for every $\lambda\in(0,1]$:
--
--   1. the set of optimal solutions of (5.1) is nonempty, and
--   2. each optimal solution $X$ is SSD-efficient in $Q$: there is no $Y\in Q$ with $Y\succ_{SSD}X$.
--
--   This is the main result of the mission: the mean–Gini model with trade-off $\lambda\le1$ never selects a portfolio that some feasible portfolio dominates in the second-degree sense, so it is consistent with risk-averse preferences.
--
--   **Formalization Note** Nonemptiness of $Q$ is not written in the paper and is added: without it no optimal solution exists. The paper's $q>1$ is a real number, so $q\ne\infty$ is part of its hypothesis. The trade-off coefficient is named `lam` because `λ` is a Lean keyword. Optimal solutions are stated as maximizers in $Q$, not through a supremum value.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 73, Theorem 5.3 (problem (5.1) and standing assumptions on Q, pp. 72–73)

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini
import Definitions.Def_DualSSD_MeanRisk_ssdEfficient

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **Theorem 5.3** (Ogryczak–Ruszczyński 2002, p. 73). Let `Q ⊆ L_q(Ω, P)`, `1 < q < ∞`, be
convex, bounded, closed and nonempty, and let `lam ∈ (0, 1]` (the paper's `λ`; `λ` is a Lean
keyword). Then the mean–Gini problem (5.1) `max_{X ∈ Q} (μ_X − lam Γ_X)` has an optimal solution
in `Q`, and every optimal solution is SSD-efficient in `Q` (no `Y ∈ Q` with `Y ≻_SSD X`).
`Q.Nonempty` is not on the page: the paper assumes it silently, and without it no optimal
solution exists. -/
theorem meanGini_optimal_exists_ssdEfficient {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (q : ENNReal) [Fact (1 ≤ q)] (hq : 1 < q) (hqtop : q ≠ ⊤)
    (Q : Set (Lp ℝ q P)) (hQconv : Convex ℝ Q) (hQbdd : Bornology.IsBounded Q)
    (hQclosed : IsClosed Q) (hQne : Q.Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∃ X ∈ Q, ∀ Z ∈ Q, mean P ⇑Z - lam * gini P ⇑Z ≤ mean P ⇑X - lam * gini P ⇑X) ∧
      ∀ X ∈ Q, (∀ Z ∈ Q, mean P ⇑Z - lam * gini P ⇑Z ≤ mean P ⇑X - lam * gini P ⇑X) →
        SSDEfficient P ((fun Z : Lp ℝ q P => (⇑Z : Ω → ℝ)) '' Q) ⇑X := by sorry

end DualSSD.MeanRisk
