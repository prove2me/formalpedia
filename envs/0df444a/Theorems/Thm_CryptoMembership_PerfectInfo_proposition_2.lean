-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_proposition_2
-- name    : CryptoMembership.PerfectInfo.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:57.151022+00:00
-- url     : https://prove2.me/theorems/281182bd-8591-4d18-87ce-282af712d231
-- title:
--   Proposition 2, pp. 15–16 (PDF 16–17) — two, one or no cutoff equilibria as A + ξ is above, at or below a threshold; log-linear price; opposite comparative statics
-- statement:
--   Consider the perfect-information setting under the standing assumptions $\eta_c\in(0,1)$, $\tau_\varepsilon,\tau_e>0$, $\rho_s\in(0,1)$. An equilibrium at fundamentals $(A,\xi)$ is a measurable purchase set $B$ and a price $P>0$ such that households buy exactly when their expected utility of trading on the platform is at least $P$, and the mass of buyers equals the mass of miners. There is a threshold $K$ such that the following hold.
--
--   **Generically two.** For all $(A,\xi)$ there are exactly two equilibria if $A+\xi>K$, exactly one if $A+\xi=K$, and none if $A+\xi<K$.
--
--   1. **Cutoff strategy.** Every equilibrium purchase set is $\{A_i\ge A^*\}$ for a cutoff $A^*$ that solves
--   $$e^{(1-\eta_c+\sqrt{\tau_\varepsilon/\tau_e})(A^*-A)}\,\Phi\Big(\eta_c\tau_\varepsilon^{-1/2}-\frac{A^*-A}{\tau_\varepsilon^{-1/2}}\Big)=e^{-A-\xi-\frac12\eta_c^2\tau_\varepsilon^{-1}-\log(1-\rho_s)},\tag{6}$$
--   and conversely every solution $A^*$ of (6) is the cutoff of an equilibrium.
--   2. **Log-linear price.** In every equilibrium with cutoff $A^*$,
--   $$\log P=\sqrt{\frac{\tau_\varepsilon}{\tau_e}}(A-A^*)-\xi-\log(1-\rho_s).$$
--   3. **Comparative statics.** Holding $\xi$ fixed and comparing $A<A'$: in the high-price equilibrium (the lowest cutoff $\underline A^*$) the price $P$, the developer's revenue $\Pi_D=\rho_s\Phi\big(\frac{A-A^*}{\tau_\varepsilon^{-1/2}}\big)P$, the ex ante utility $U_0$ and the mass of buyers are strictly larger at $A'$; in the low-price equilibrium (the highest cutoff $\bar A^*$) they are all strictly smaller. Holding $A$ fixed and comparing $\xi<\xi'$, the mass of buyers is strictly larger at $\xi'$ in the high-price equilibrium and strictly smaller in the low-price equilibrium.
--   4. **No purchase for small fundamentals.** For every $\xi$ there is $A_0$ such that no equilibrium exists when $A<A_0$, and for every $A$ there is $\xi_0$ such that no equilibrium exists when $\xi<\xi_0$.
--
--   The proposition shows that platform adoption has two self-confirming equilibria with opposite responses to fundamentals: when many households buy, a stronger platform raises the price; when few buy, it lowers it.
--
--   **Formalization Note** "Generically two cutoff equilibria" is stated as the trichotomy in $A+\xi$ that the proof establishes (two intersections, a knife-edge tangency, or none), counted with `Set.encard` over all pairs $(B,P)$; equal purchase sets force equal prices by (13), so pairs are counted by their cutoffs. The high- and low-price equilibria are the cutoff equilibria with the smallest and largest cutoff. Statements in part 3 compare two equilibria of the same kind at two parameter values at which they exist; the page claims monotonicity in $\xi$ only for the number of buyers, and only that is stated. "No household buys" is rendered as "no equilibrium exists": with $P>0$ the mass of miners is positive, so the empty purchase set cannot clear the market. The mining cost is $e^{-(\xi+e_i)}$ as in (4); display (5)'s $e^{-\xi+e_i}$ gives the same mass of miners. The proof's line "$dU_0/dA>0$" for the low-price equilibrium (A.2, p. 35) contradicts part 3; part 3 is stated as printed in the proposition.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), pp. 15–16 (PDF 16–17), Proposition 2; proof A.2, pp. 32–35 (PDF 33–36)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem proposition_2 (P : Params) (hP : P.Standing) :
    ∃ K : ℝ,
      -- "generically two": exactly two / one / no equilibria as A + ξ is above / at / below K
      (∀ A xi : ℝ, (equilibria P A xi).encard = 2 ↔ K < A + xi) ∧
      (∀ A xi : ℝ, (equilibria P A xi).encard = 1 ↔ A + xi = K) ∧
      (∀ A xi : ℝ, equilibria P A xi = ∅ ↔ A + xi < K) ∧
      -- part 1: every equilibrium is a cutoff equilibrium whose cutoff solves (6), and conversely
      (∀ (A xi : ℝ) (B : Set ℝ) (price : ℝ), IsEquilibrium P A xi B price →
          ∃ a : ℝ, B = Set.Ici a ∧ lhs15 P (a - A) = rhs15 P A xi) ∧
      (∀ A xi a : ℝ, lhs15 P (a - A) = rhs15 P A xi →
          ∃ price : ℝ, IsEquilibrium P A xi (Set.Ici a) price) ∧
      -- part 2: log-linear price
      (∀ A xi a price : ℝ, IsEquilibrium P A xi (Set.Ici a) price →
          Real.log price = Real.sqrt (P.tauEps / P.tauE) * (A - a) - xi - Real.log (1 - P.rho)) ∧
      -- part 3, in A (ξ fixed): high-price equilibrium increasing, low-price decreasing
      (∀ xi A A' a price a' price' : ℝ, A < A' →
          IsHighPriceEq P A xi a price → IsHighPriceEq P A' xi a' price' →
          price < price' ∧
          devRevenue P A (Set.Ici a) price < devRevenue P A' (Set.Ici a') price' ∧
          exAnteUtility P A (Set.Ici a) price < exAnteUtility P A' (Set.Ici a') price' ∧
          buyerMass P A (Set.Ici a) < buyerMass P A' (Set.Ici a')) ∧
      (∀ xi A A' a price a' price' : ℝ, A < A' →
          IsLowPriceEq P A xi a price → IsLowPriceEq P A' xi a' price' →
          price' < price ∧
          devRevenue P A' (Set.Ici a') price' < devRevenue P A (Set.Ici a) price ∧
          exAnteUtility P A' (Set.Ici a') price' < exAnteUtility P A (Set.Ici a) price ∧
          buyerMass P A' (Set.Ici a') < buyerMass P A (Set.Ici a)) ∧
      -- part 3, in ξ (A fixed): the number of buyers
      (∀ A xi xi' a price a' price' : ℝ, xi < xi' →
          IsHighPriceEq P A xi a price → IsHighPriceEq P A xi' a' price' →
          buyerMass P A (Set.Ici a) < buyerMass P A (Set.Ici a')) ∧
      (∀ A xi xi' a price a' price' : ℝ, xi < xi' →
          IsLowPriceEq P A xi a price → IsLowPriceEq P A xi' a' price' →
          buyerMass P A (Set.Ici a') < buyerMass P A (Set.Ici a)) ∧
      -- part 4: no household buys if A or ξ is sufficiently small
      (∀ xi : ℝ, ∃ A₀ : ℝ, ∀ A : ℝ, A < A₀ → equilibria P A xi = ∅) ∧
      (∀ A : ℝ, ∃ ξ₀ : ℝ, ∀ xi : ℝ, xi < ξ₀ → equilibria P A xi = ∅) := by sorry

end CryptoMembership.PerfectInfo
