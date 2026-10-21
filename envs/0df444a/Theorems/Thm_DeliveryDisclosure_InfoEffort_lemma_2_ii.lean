-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_lemma_2_ii
-- name    : DeliveryDisclosure.InfoEffort.lemma_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:17.641442+00:00
-- url     : https://prove2.me/theorems/60010e33-c574-422e-9618-fbfe5beb51d2
-- title:
--   Lemma 2, item 2, p. 13 — if (19) fails at ϕ ∈ (0, 1), then λ*(ϕ) and Π*(ϕ) are strictly increasing there (demand and profit parts)
-- statement:
--   Under the standing assumptions, let $\phi\in(0,1)$ and suppose condition (19) fails at $\phi$:
--   $$\frac{b\,\omega_\theta^2}{\beta_r^2\phi}\;<\;V^*(\phi)-V_e.$$
--   Then the optimal demand $\lambda^*$ and the optimal profit $\Pi^*$ are both differentiable at $\phi$, with strictly positive derivatives.
--
--   When consumers' surplus over the outside option dominates the effort cost, more precise information attracts demand and raises profit.
--
--   **Formalization Note** Only the demand and profit parts of item 2 are stated. Its printed claims that $p^*(\phi)$ increases and that $V$ decreases are false: with $\Lambda=24.8628$, $\alpha=14.8413$, $\beta_r=4.0821$, $\beta_t=0.502$, $\rho=1.6712$, $V_e=2.3612$, $\omega_Y=3.1167$, $\mu=30.66$, $c=3.0319$, $b=0.4359$, condition (19) fails for $\phi\in[0.5,0.9]$ while $p^*$ falls and $V$ rises. The parts on $t^*$, $q^*$, $E(R^*)$ and $V>V_e$ are not used by Theorem 1 and are not formalized.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. 13, Lemma 2, item 2 (λ* and Π* parts), condition (19); proof pp. OA-5 – OA-7

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Lemma 2, item 2, p. 13, demand and profit parts: if condition (19) fails at `ϕ ∈ (0, 1)`, then
the optimal demand `λ*` and the optimal profit `Π*` are differentiable at `ϕ` with positive
derivatives. -/
theorem lemma_2_ii (P : Params) (hP : Standing P) (ϕ : ℝ) (hϕ : ϕ ∈ Set.Ioo (0 : ℝ) 1)
    (h19 : P.b * ωθ P ϕ ^ 2 / (P.βr ^ 2 * ϕ) < optV P ϕ - P.Ve) :
    (∃ d > 0, HasDerivAt (optDem P) d ϕ) ∧ (∃ d > 0, HasDerivAt (optProfit P) d ϕ) := by sorry

end DeliveryDisclosure.InfoEffort
