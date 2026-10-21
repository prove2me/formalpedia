-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_eq_35
-- name    : DeliveryDisclosure.InfoEffort.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:36.77342+00:00
-- url     : https://prove2.me/theorems/1210e380-d0b9-4377-8268-a4c194ba32ce
-- title:
--   Eq. (35), proof of Theorem 1, p. OA-8 — h has negative derivative at every ϕ0 ∈ (0, 1) where h(ϕ0) < 0
-- statement:
--   Under the standing assumptions, let $\phi_0\in(0,1)$ with $h(\phi_0)<0$, i.e. condition (19) fails at $\phi_0$. Then $h$ is differentiable at $\phi_0$ and
--   $$\frac{\partial h(\phi)}{\partial\phi}\Big|_{\phi=\phi_0}<0.$$
--
--   This is the local step of the single-crossing argument: wherever condition (19) fails, it fails more and more as the effort increases.
--
--   **Formalization Note** The page derives (35) at one point $\phi_0$ and then repeats the argument at $\phi_1,\phi_2,\dots$ ("Similar to our proof of (35)"); the statement is therefore given at every point where $h$ is negative.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. OA-8, proof of Theorem 1, eq. (35)

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Eq. (35), proof of Theorem 1, p. OA-8: at every `ϕ₀ ∈ (0, 1)` with `h(ϕ₀) < 0`, `h` is
differentiable with negative derivative. -/
theorem eq_35 (P : Params) (hP : Standing P) (ϕ0 : ℝ) (hϕ0 : ϕ0 ∈ Set.Ioo (0 : ℝ) 1)
    (hneg : h P ϕ0 < 0) :
    ∃ d < 0, HasDerivAt (h P) d ϕ0 := by sorry

end DeliveryDisclosure.InfoEffort
