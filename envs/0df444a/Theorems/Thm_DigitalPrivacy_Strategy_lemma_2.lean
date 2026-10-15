-- Prove2me | Theorems.Thm_DigitalPrivacy_Strategy_lemma_2
-- name    : DigitalPrivacy.Strategy.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:39.420347+00:00
-- url     : https://prove2.me/theorems/8a7997a1-89ee-4a27-b191-44d2caf98dd0
-- title:
--   Lemma 2, p. 29 — for fixed protection C, the optimal collection is −κ(C)+√(κ(C)²+C(1−β)) < 1 if C < C_l, and 1 if C > C_l
-- statement:
--   Let $0 \le \beta < 1$, $0 < \rho < 1$, $\psi > 0$, $0 \le P \le 1$, and fix a protection level $C > 0$. Let
--   $$\kappa(C) = \frac{1-P-P\rho C(1-\beta)}{P+(1-P)\rho}, \qquad C_l = \frac{1}{1-\beta}\,\frac{2+\rho-P(1+\rho)}{P+\rho+P\rho}, \qquad \xi^*(C) = -\kappa(C) + \sqrt{\kappa(C)^2 + C(1-\beta)} .$$
--   Then:
--
--   1. if $C < C_l$, then $0 \le \xi^*(C) < 1$ and $\xi^*(C)$ is the unique maximizer of $\xi \mapsto \Pi(\xi, C)$ over $[0, 1]$ (the business stores part of the information);
--   2. if $C > C_l$, then $\xi = 1$ is the unique maximizer of $\xi \mapsto \Pi(\xi, C)$ over $[0, 1]$ (the business stores all the information);
--   3. $C \mapsto \xi^*(C)$ is strictly increasing on $(0, C_l)$.
--
--   This is the business's best collection response to a given protection level; together with Lemma 1 it reduces Theorem 1 to comparing the intersections of the two best responses.
--
--   **Formalization Note** The statement assumes $C > 0$ and $\rho > 0$, which the page leaves implicit: at $C = 0$, $P = 1$ every $\xi$ gives the same profit, and $\rho > 0$ makes $P + (1-P)\rho > 0$, the denominator of $\kappa$. At $C = C_l$ both branches give $\xi = 1$, so the case is omitted as on the page. The assumption $\psi > 0$ comes from the shared parameter predicate and is not used here.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 29, Lemma 2; proof Online App. B

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Strategy

/-- Lemma 2, p. 29: for a fixed protection level `C > 0` (and `ρ > 0`), if `C < C_l` the unique
maximizer of `ξ ↦ Π(ξ, C)` over `[0, 1]` is `ξ*(C) = −κ(C) + √(κ(C)² + C(1 − β)) < 1`, and if
`C > C_l` it is `1`; moreover `−κ(C) + √(κ(C)² + C(1 − β))` is strictly increasing in `C` on
`(0, C_l)`. -/
theorem lemma_2 (β ρ ψ P C : ℝ) (hB : Basic β ρ ψ P) (hρ : 0 < ρ) (hC : 0 < C) :
    (C < Cl β ρ P →
      xiBR β ρ P C ∈ Set.Ico (0 : ℝ) 1 ∧
      ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        profit β ρ ψ P ξ C ≤ profit β ρ ψ P (xiBR β ρ P C) C ∧
        (profit β ρ ψ P ξ C = profit β ρ ψ P (xiBR β ρ P C) C → ξ = xiBR β ρ P C)) ∧
    (Cl β ρ P < C →
      ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        profit β ρ ψ P ξ C ≤ profit β ρ ψ P 1 C ∧
        (profit β ρ ψ P ξ C = profit β ρ ψ P 1 C → ξ = 1)) ∧
    StrictMonoOn (xiBR β ρ P) (Set.Ioo 0 (Cl β ρ P)) := by sorry

end DigitalPrivacy.Strategy
