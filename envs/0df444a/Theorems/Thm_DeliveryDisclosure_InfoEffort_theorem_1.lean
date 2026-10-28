-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_theorem_1
-- name    : DeliveryDisclosure.InfoEffort.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:22.88651+00:00
-- url     : https://prove2.me/theorems/4690e370-4abe-4054-9648-9bbd043600a1
-- title:
--   Theorem 1, p. 15 — the optimal information-quality effort is 0 if bω_Y²/β_r² ≥ V1 − Ve, and otherwise the better of 0 and 1
-- statement:
--   Under the standing assumptions, let $\Pi^*(\phi)$ be the firm's optimal profit at information-quality effort $\phi\in[0,1]$, and let condition (23) be
--   $$\frac{b\,\omega_Y^2}{\beta_r^2}\;\ge\;V_1-V_e,$$
--   with $V_1$ the deterministic utility at the optimal plan under full effort. Then:
--
--   1. If (23) holds, $\Pi^*$ is strictly decreasing on $[0,1]$, so $\phi^*=0$ is the unique optimal effort.
--   2. If (23) fails, there is $\phi_0\in(0,1)$ such that $\Pi^*$ is strictly decreasing on $[0,\phi_0]$ and strictly increasing on $[\phi_0,1]$.
--   3. In either case,
--   $$\Pi^*(\phi)\;<\;\max\{\Pi^*(0),\,\Pi^*(1)\}\qquad\text{for all }\phi\in(0,1),$$
--   so every optimal effort belongs to $\arg\max_{\phi\in\{0,1\}}\Pi^*(\phi)$.
--
--   The firm should never invest partially in the quality of its delivery-performance information: it either makes no effort or full effort, and (23) identifies when no effort is optimal.
--
--   **Formalization Note** The paper's $0^+$ and $1^-$ are read as the endpoints $0$ and $1$ of the closed effort range $[0,1]$ of p. 5. Item 2 records the shape established in the proof (p. OA-9: "Π*(ϕ) decreases with ϕ over the range (0, ϕ0] but Π*(ϕ) increases with ϕ over the range (ϕ0, 1)").
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. 15, Theorem 1 and condition (23); proof pp. OA-7 – OA-9

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Theorem 1, p. 15: the optimal information-quality effort is an endpoint of `[0, 1]`.
(1) If condition (23) holds, `Π*` strictly decreases on `[0, 1]`, so `ϕ* = 0`.
(2) Otherwise `Π*` strictly decreases on `[0, ϕ₀]` and strictly increases on `[ϕ₀, 1]` for some
`ϕ₀ ∈ (0, 1)`.
Every interior effort has strictly less profit than at least one endpoint. -/
theorem theorem_1 (P : Params) (hP : Standing P) :
    (cond23 P → StrictAntiOn (optProfit P) (Set.Icc 0 1)) ∧
      (¬ cond23 P → ∃ ϕ0 ∈ Set.Ioo (0 : ℝ) 1,
        StrictAntiOn (optProfit P) (Set.Icc 0 ϕ0) ∧ StrictMonoOn (optProfit P) (Set.Icc ϕ0 1)) ∧
      ∀ ϕ ∈ Set.Ioo (0 : ℝ) 1, optProfit P ϕ < max (optProfit P 0) (optProfit P 1) := by sorry

end DeliveryDisclosure.InfoEffort
