-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_single_crossing
-- name    : DeliveryDisclosure.InfoEffort.single_crossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:37.100557+00:00
-- url     : https://prove2.me/theorems/0a3ed8cc-b5c9-4bc2-b013-4a4a29991893
-- title:
--   Proof of Theorem 1, pp. OA-8 – OA-9 — once h(ϕ0) < 0 for some ϕ0 ∈ (0, 1), h stays negative on [ϕ0, 1)
-- statement:
--   Under the standing assumptions, let $\phi_0\in(0,1)$ with $h(\phi_0)<0$. Then
--   $$h(\phi)<0\qquad\text{for all }\phi\in[\phi_0,1).$$
--
--   So $h$ crosses zero at most once, and only downward: condition (19) holds on an initial segment of the efforts and fails on the rest.
--
--   **Formalization Note** The page's sentence ends "for all values of ϕ in (ϕ0, 1)" at the top of p. OA-9; the statement here also includes $\phi_0$ itself, where $h<0$ by hypothesis.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), pp. OA-8 – OA-9, proof of Theorem 1

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Proof of Theorem 1, pp. OA-8 – OA-9: once `h` is negative at `ϕ₀ ∈ (0, 1)`, it stays negative
on `[ϕ₀, 1)`. -/
theorem single_crossing (P : Params) (hP : Standing P) (ϕ0 : ℝ) (hϕ0 : ϕ0 ∈ Set.Ioo (0 : ℝ) 1)
    (hneg : h P ϕ0 < 0) :
    ∀ ϕ ∈ Set.Ico ϕ0 1, h P ϕ < 0 := by sorry

end DeliveryDisclosure.InfoEffort
