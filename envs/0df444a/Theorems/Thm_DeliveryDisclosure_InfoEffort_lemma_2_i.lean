-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_lemma_2_i
-- name    : DeliveryDisclosure.InfoEffort.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:29.606574+00:00
-- url     : https://prove2.me/theorems/c6d72da7-c7fb-4a1e-b339-4ac1024f1168
-- title:
--   Lemma 2, item 1, p. 13 — if (19) holds at ϕ ∈ (0, 1), then Π*(ϕ) is non-increasing there (profit part only)
-- statement:
--   Under the standing assumptions, let $\phi\in(0,1)$ and suppose condition (19) holds at $\phi$:
--   $$\frac{b\,\omega_\theta^2}{\beta_r^2\phi}\;\ge\;V^*(\phi)-V_e,$$
--   where $V^*(\phi)$ is the deterministic utility at the optimal plan. Then the optimal profit $\Pi^*$ is differentiable at $\phi$ and its derivative there is $\le 0$.
--
--   When the information-quality cost dominates the consumers' surplus over the outside option, more effort lowers profit.
--
--   **Formalization Note** Only the profit part of item 1 is stated. Its printed claims that $t^*(\phi)$ and $\lambda^*(\phi)$ decrease (and so that $q^*$ increases) are false: with $\Lambda=42.3942$, $\alpha=3.6095$, $\beta_r=5.7705$, $\beta_t=6.9509$, $\rho=3.3859$, $V_e=5.4836$, $\omega_Y=6.2174$, $\mu=56.5477$, $c=3.5816$, $b=2.3412$, condition (19) holds for $\phi\in[0.6,0.9]$ while $\lambda^*$ and $t^*$ rise. The parts on $p^*$, $q^*$, $E(R^*)$ and condition (20) are not formalized.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. 13, Lemma 2, item 1 (Π* part), condition (19); proof pp. OA-5 – OA-7

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Lemma 2, item 1, p. 13, profit part: if condition (19), `bω_θ²/(β_r²ϕ) ≥ V − V_e`, holds at
`ϕ ∈ (0, 1)` (with `V` at the optimal plan), then `Π*` is differentiable at `ϕ` with non-positive
derivative. -/
theorem lemma_2_i (P : Params) (hP : Standing P) (ϕ : ℝ) (hϕ : ϕ ∈ Set.Ioo (0 : ℝ) 1)
    (h19 : optV P ϕ - P.Ve ≤ P.b * ωθ P ϕ ^ 2 / (P.βr ^ 2 * ϕ)) :
    ∃ d ≤ 0, HasDerivAt (optProfit P) d ϕ := by sorry

end DeliveryDisclosure.InfoEffort
