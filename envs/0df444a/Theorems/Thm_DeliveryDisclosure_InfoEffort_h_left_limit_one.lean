-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_h_left_limit_one
-- name    : DeliveryDisclosure.InfoEffort.h_left_limit_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:28.275982+00:00
-- url     : https://prove2.me/theorems/6b010665-41ec-446d-bc7d-bba70fcea639
-- title:
--   Proof of Theorem 1, p. OA-9 — h(1⁻) = bω_Y/β_r² − (V1 − Ve)/ω_Y, and (23) holds exactly when h(1⁻) ≥ 0
-- statement:
--   Under the standing assumptions, let $V_1=V^*(1)$ be the deterministic utility at the optimal plan under full effort. Then
--   $$h(1^-)=\lim_{\phi\to 1^-}h(\phi)=\frac{b\,\omega_Y}{\beta_r^2}-\frac{V_1-V_e}{\omega_Y},$$
--   and condition (23), $b\omega_Y^2/\beta_r^2\ge V_1-V_e$, holds if and only if this limit is $\ge 0$.
--
--   This connects the single-crossing behaviour of $h$ to the closed-form test (23) of Theorem 1.
--
--   **Formalization Note** The page defines $V_1$ as $\lim_{\phi\to1}V$; here $V_1$ is $V$ at the optimal plan for $\phi=1$, which is a point of the effort range, and the limit statement makes the two readings agree.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. OA-9, proof of Theorem 1; condition (23), p. 15

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Proof of Theorem 1, p. OA-9: `h(1⁻) = bω_Y/β_r² − (V₁ − V_e)/ω_Y`, and condition (23) holds
exactly when this limit is non-negative. -/
theorem h_left_limit_one (P : Params) (hP : Standing P) :
    Filter.Tendsto (h P) (nhdsWithin 1 (Set.Iio 1))
        (nhds (P.b * P.ωY / P.βr ^ 2 - (optV P 1 - P.Ve) / P.ωY)) ∧
      (cond23 P ↔ 0 ≤ P.b * P.ωY / P.βr ^ 2 - (optV P 1 - P.Ve) / P.ωY) := by sorry

end DeliveryDisclosure.InfoEffort
