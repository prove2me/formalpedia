-- Prove2me | Theorems.Thm_CongestedPlatforms_Surge_proposition_1_d
-- name    : CongestedPlatforms.Surge.proposition_1_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:23.849981+00:00
-- url     : https://prove2.me/theorems/db0e29b8-5aea-4200-8771-6c2f4588f89c
-- title:
--   Proposition 1(d), p. 16 (corrected: c > 0, c < 1/2; D = S on γ = λ/2) — in Region (d) the unique symmetric equilibrium price is c + √(λγ/2), with full coverage
-- statement:
--   Take $\alpha=1$, a market size $\lambda>0$ and a commission $c\in(0,\tfrac12)$, and suppose $(\lambda,\gamma)$ lies in Region (d):
--   $$\gamma<\frac{(\tfrac12-c)^2}{2\lambda}\qquad\text{and}\qquad\gamma\ge\frac{\lambda}{2}.$$
--   Let $p^*=c+\sqrt{\lambda\gamma/2}$. Then:
--   1. a price $p$ is a symmetric Nash equilibrium of the pricing game if and only if $p=p^*$;
--   2. at $(p^*,p^*)$ the market is fully covered: $d^P(p^*)+d^P(p^*)>\lambda$;
--   3. if $\gamma>\lambda/2$, equilibrium demand is strictly lower than equilibrium supply, $D(p^*,p^*)<S(p^*,p^*)$;
--   4. if $\gamma=\lambda/2$, they are equal.
--
--   In this region the platforms compete head to head for the customers in the middle of the line and still have spare driver capacity. This statement formalizes part (d) of Proposition 1; the clause of the same printed sentence about Region (c) belongs to part (c), which is not posed in this mission.
--
--   **Formalization Note** Same equilibrium notion as Proposition 1(a): action set $[c,1]$, supply constraint on the deviations and on $p^*$.
--
--   Differences from the source:
--   - correction: $c\ge0$ → $c>0$; reason: at $\alpha=1$ the profit $c\min\{D,S\}$ is identically $0$ when $c=0$, so every price satisfying (3.6) is an equilibrium and uniqueness fails.
--   - correction: Region (d) for any $c$ → Region (d) with $c<\tfrac12$; reason: for $c>\tfrac12$ the printed region is nonempty but the formula is wrong; counterexample $c=0.9$, $\lambda=\gamma=0.2$, where the printed $p^*\approx1.041$ exceeds $\bar p=1$ and the true equilibrium is $\approx0.935$.
--   - correction: "equilibrium demand strictly lower than equilibrium supply" → strict when $\gamma>\lambda/2$, equality when $\gamma=\lambda/2$; reason: the boundary $\gamma=\lambda/2$ is in the printed region and $D=S$ there; counterexample $c=1/10$, $\lambda=1/5$, $\gamma=1/10$.
--   - reading: "the following are the symmetric equilibrium prices" → $p$ is a symmetric Nash equilibrium iff $p=p^*$; reason: the formula names the equilibrium whose existence and uniqueness Theorem 1 asserts.
--   - reading: action set $[\underline p,\bar p]$ → $[c,1]$; reason: the natural bounds of pp. 11, 13 at $\alpha=1$.
--   - reading: the supply constraint (3.6) restricts the deviations → it also holds at $p^*$; reason: "The prices selected by the platforms must also satisfy the following supply constraint" (p. 14).
--   - encoding: "the platforms fully cover the market" → $d^P(p^*)+d^P(p^*)>\lambda$; reason: this is the Case F condition of Lemma 1.
-- source:
--   Bernstein, DeCroix, Keskin, Competition between Two-Sided Platforms under Demand and Supply Congestion Effects, SSRN 3250224, version of September 16, 2019, p. 16, Proposition 1(d); proof: Online Supplement, pp. 2–4 (PDF 34–36)

import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem proposition_1_d (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) (hD2 : lam / 2 ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔ p = c + Real.sqrt (lam * γ / 2)) ∧
    (lam < dP lam γ 1 c (c + Real.sqrt (lam * γ / 2)) + dP lam γ 1 c (c + Real.sqrt (lam * γ / 2))) ∧
    (lam / 2 < γ →
      D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) <
        S lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) ∧
    (γ = lam / 2 →
      D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) =
        S lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) := by sorry

end CongestedPlatforms.Surge
