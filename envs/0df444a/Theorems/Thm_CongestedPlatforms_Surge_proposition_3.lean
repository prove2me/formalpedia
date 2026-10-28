-- Prove2me | Theorems.Thm_CongestedPlatforms_Surge_proposition_3
-- name    : CongestedPlatforms.Surge.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:21.694048+00:00
-- url     : https://prove2.me/theorems/7230824c-1a0b-48cc-a549-03cb78755ee3
-- title:
--   Proposition 3, p. 18 (corrected: c > 0) — surge pricing lowers customer and raises driver utility, and for surges up to Λ(λ, γ) beats keeping the old price for both
-- statement:
--   Take $\alpha=1$, a commission $c\in(0,1)$, a congestion sensitivity $\gamma$ and a market size $\lambda>0$ such that $(\lambda,\gamma)$ lies in Region (a) or Region (d) of Proposition 1 (the supply-unconstrained regions). Write $p^*(\lambda)$ for a symmetric equilibrium price at market size $\lambda$, and for a common price $p$ write
--   $$u_{d0}(p,\lambda)=1-v-p-\gamma\rho(p,\lambda)^2,\quad u_{d1}(p,\lambda)=v-p-\gamma\rho(p,\lambda)^2,\quad u_s(p,\lambda)=-k+(p-c)\rho(p,\lambda)$$
--   for the utilities of a customer at location $v$ and of a driver with cost $k$, where $\rho(p,\lambda)=D(p,p)/S(p,p)$ is the utilization at market size $\lambda$. Then:
--
--   1. a symmetric equilibrium exists at $\lambda$;
--   2. **(i)** for every $\hat\lambda>\lambda$ with $(\hat\lambda,\gamma)$ in Region (a) or (d), a symmetric equilibrium exists at $\hat\lambda$, and for all such equilibrium prices, all $v$, $k$ and $i\in\{0,1\}$,
--   $$u_{di}(p^*(\lambda),\lambda)>u_{di}(p^*(\hat\lambda),\hat\lambda)\qquad\text{and}\qquad u_s(p^*(\lambda),\lambda)<u_s(p^*(\hat\lambda),\hat\lambda);$$
--   3. **(ii)** there is $\Lambda(\lambda,\gamma)\in(\lambda,\infty]$ such that for every $\hat\lambda\in(\lambda,\Lambda(\lambda,\gamma)]$ with $(\hat\lambda,\gamma)$ in Region (a) or (d), for all equilibrium prices, all $v$, $k$ and $i\in\{0,1\}$,
--   $$u_{di}(p^*(\lambda),\hat\lambda)<u_{di}(p^*(\hat\lambda),\hat\lambda)\qquad\text{and}\qquad u_s(p^*(\lambda),\hat\lambda)<u_s(p^*(\hat\lambda),\hat\lambda).$$
--
--   Part (i) says that when demand surges and the platforms re-optimize, customers lose and drivers gain relative to the old market. Part (ii) says that for moderate surges, re-optimizing ("surge pricing") makes both customers and drivers better off than keeping the old price in the new market, because the higher price attracts drivers and relieves congestion.
--
--   **Formalization Note** The symmetric equilibrium is that of the Setting (action set $[c,1]$, supply constraint (3.6) on the deviations and on the equilibrium price). $\Lambda$ is an extended real, so $\Lambda=+\infty$ is allowed. At a symmetric profile both platforms have the same utilization, so one driver utility covers $i\in\{0,1\}$.
--
--   Differences from the source:
--   - correction: $c\ge0$ → $c>0$; reason: at $\alpha=1$ the profit $c\min\{D,S\}$ is identically $0$ when $c=0$, so every price satisfying (3.6) is an equilibrium; counterexample $c=0$, $\lambda=\gamma=1$, $\hat\lambda=1.1$ (both in Region (a)) with $p^*(\lambda)=p^*(\hat\lambda)=1/2$, where the strict inequalities become equalities.
--   - generalization: a purchasing customer's location $v\in[0,1]$ and a driver's cost $k\in[0,1]$ (suppressed in $u_{di}(p,\lambda)$, $u_{si}(p,\lambda)$) → all $v,k\in\mathbb R$; reason: the inequalities hold for each fixed $v$, $k$, whose terms cancel, so the statement specializes to $v,k\in[0,1]$.
--   - encoding: "$p^*(\lambda)$, the equilibrium price characterized in Theorem 1" → a symmetric equilibrium exists at $\lambda$ (and at each $\hat\lambda$), and the inequalities hold for every symmetric equilibrium price; reason: with Theorem 1's uniqueness this is the same statement, and the existence clauses keep it from being vacuous.
--   - encoding: $\Lambda(\lambda,\gamma)\in(\lambda,\infty]$ and $\hat\lambda\in(\lambda,\Lambda]$ → $\Lambda$ an extended real with $\lambda<\Lambda$, and $\lambda<\hat\lambda$, $\hat\lambda\le\Lambda$; reason: same instances.
--   - encoding: "for $i\in\{0,1\}$" for drivers → one driver utility; reason: at a symmetric profile $u_{s0}=u_{s1}$.
--   - reading: action set $[\underline p,\bar p]$ and $\underline p<\bar p$ → $[c,1]$ and $c<1$; reason: the natural bounds of pp. 11, 13 at $\alpha=1$.
--   - reading: the supply constraint (3.6) restricts the deviations → it also holds at the equilibrium price; reason: "The prices selected by the platforms must also satisfy the following supply constraint" (p. 14).
-- source:
--   Bernstein, DeCroix, Keskin, Competition between Two-Sided Platforms under Demand and Supply Congestion Effects, SSRN 3250224, version of September 16, 2019, p. 18, Proposition 3; proof: Online Supplement, pp. 5–6 (PDF 37–38)

import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem proposition_3 (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) :
    (∃ p : ℝ, IsSymNE lam γ 1 c p) ∧
    (∀ lamHat : ℝ, lam < lamHat → (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
      (∃ q : ℝ, IsSymNE lamHat γ 1 c q) ∧
      ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
        uD0 lamHat γ 1 c v q < uD0 lam γ 1 c v p ∧
        uD1 lamHat γ 1 c v q < uD1 lam γ 1 c v p ∧
        uS lam γ 1 c k p < uS lamHat γ 1 c k q) ∧
    (∃ Λ : EReal, (lam : EReal) < Λ ∧
      ∀ lamHat : ℝ, lam < lamHat → (lamHat : EReal) ≤ Λ →
        (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
        ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
          uD0 lamHat γ 1 c v p < uD0 lamHat γ 1 c v q ∧
          uD1 lamHat γ 1 c v p < uD1 lamHat γ 1 c v q ∧
          uS lamHat γ 1 c k p < uS lamHat γ 1 c k q) := by sorry

end CongestedPlatforms.Surge
