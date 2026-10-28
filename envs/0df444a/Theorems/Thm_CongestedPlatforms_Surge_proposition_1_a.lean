-- Prove2me | Theorems.Thm_CongestedPlatforms_Surge_proposition_1_a
-- name    : CongestedPlatforms.Surge.proposition_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:17.529986+00:00
-- url     : https://prove2.me/theorems/317e3d52-2457-4921-a277-b858666489fb
-- title:
--   Proposition 1(a), p. 16 (corrected: c > 0; D = S on the boundary γ = λ(1−c)/(1+2λ)) — in Region (a) the unique symmetric equilibrium price is c + √(λ²γ² + λγ(1 − c)) − λγ, with partial coverage
-- statement:
--   Take $\alpha=1$ (the standing assumption of §4.1), a market size $\lambda>0$ and a commission $c\in(0,1)$. Suppose
--   $$\gamma\ge\frac{(\tfrac12-c)^2}{2\lambda}\ \text{ or }\ c\ge\tfrac12,\qquad\text{and}\qquad \gamma\ge\frac{\lambda(1-c)}{1+2\lambda},$$
--   which contains Region (a) of Proposition 1. Let
--   $$p^*=c+\sqrt{\lambda^2\gamma^2+\lambda\gamma(1-c)}-\lambda\gamma.$$
--   Then:
--   1. a price $p$ is a symmetric Nash equilibrium of the pricing game if and only if $p=p^*$;
--   2. at $(p^*,p^*)$ the market is partially covered: $d^P(p^*)+d^P(p^*)\le\lambda$;
--   3. if $\gamma>\lambda(1-c)/(1+2\lambda)$, equilibrium demand is strictly lower than equilibrium supply, $D(p^*,p^*)<S(p^*,p^*)$;
--   4. if $\gamma=\lambda(1-c)/(1+2\lambda)$, they are equal.
--
--   In this region the two platforms behave as local monopolies with spare driver capacity; together with Proposition 1(d) this pins down the equilibrium price in every supply-unconstrained market, which Proposition 3 compares across market sizes.
--
--   **Formalization Note** The symmetric equilibrium is taken on the action set $[c,1]$ with the supply constraint (3.6) imposed on the deviations and on $p^*$ itself; see the Setting.
--
--   Differences from the source:
--   - correction: $c\ge0$ → $c>0$; reason: at $\alpha=1$ the profit is $c\min\{D,S\}$, identically $0$ when $c=0$, so every price satisfying (3.6) is an equilibrium; counterexample $c=0$, $\lambda=\gamma=1$ (Region (a)), where $p=1/2$ is an equilibrium but $p^*=\sqrt2-1$.
--   - correction: "the equilibrium demand is strictly lower than equilibrium supply" → strict when $\gamma>\lambda(1-c)/(1+2\lambda)$, equality when $\gamma=\lambda(1-c)/(1+2\lambda)$; reason: the printed region contains this boundary, where $D=S$; counterexample $c=1/5$, $\lambda=1$, $\gamma=4/15$, where $p^*-c=4/15$ and $\rho=1$.
--   - generalization: $\gamma\ge(\tfrac12-c)^2/(2\lambda)$ → $\gamma\ge(\tfrac12-c)^2/(2\lambda)$ or $c\ge\tfrac12$; reason: for $c\ge\tfrac12$ the market is partially covered at $p^*$ whatever $\gamma$ is, and the printed condition is the first disjunct, so the statement specializes to the printed region.
--   - reading: "the following are the symmetric equilibrium prices" → $p$ is a symmetric Nash equilibrium iff $p=p^*$; reason: the formula names the equilibrium, whose existence and uniqueness Theorem 1 asserts.
--   - reading: action set $[\underline p,\bar p]$ and the restriction $\underline p<\bar p$ → $[c,1]$ and $c<1$; reason: the natural bounds of pp. 11, 13 at $\alpha=1$.
--   - reading: the supply constraint (3.6) restricts the deviations → it also holds at $p^*$; reason: "The prices selected by the platforms must also satisfy the following supply constraint" (p. 14).
--   - encoding: "the platforms partially cover the market" → $d^P(p^*)+d^P(p^*)\le\lambda$; reason: this is the Case P condition of Lemma 1.
-- source:
--   Bernstein, DeCroix, Keskin, Competition between Two-Sided Platforms under Demand and Supply Congestion Effects, SSRN 3250224, version of September 16, 2019, p. 16, Proposition 1(a); proof: Online Supplement, pp. 2–3 (PDF 34–35)

import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem proposition_1_a (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hA1 : (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c) (hA2 : lam * (1 - c) / (1 + 2 * lam) ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔
      p = c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ∧
    (dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) +
        dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ≤ lam) ∧
    (lam * (1 - c) / (1 + 2 * lam) < γ →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) <
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) ∧
    (γ = lam * (1 - c) / (1 + 2 * lam) →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) =
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) := by sorry

end CongestedPlatforms.Surge
