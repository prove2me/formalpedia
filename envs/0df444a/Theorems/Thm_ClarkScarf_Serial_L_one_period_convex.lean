-- Prove2me | Theorems.Thm_ClarkScarf_Serial_L_one_period_convex
-- name    : ClarkScarf.Serial.L_one_period_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:27:56.322805+00:00
-- url     : https://prove2.me/theorems/b331496f-b344-4cc3-946b-fc3b6b0112b3
-- title:
--   §2, p. 478, item 2 — the discounted one-period cost α∫∫L(y−t₁−t₂)φφ is convex (lead time 2)
-- statement:
--   Let $L$ be the expected one-period holding and shortage cost (1) at installation 1, with holding and shortage costs $h,p\ge0$, demand density $\varphi$ on $(0,\infty)$ with finite mean, and discount factor $\alpha\ge0$. Then the expected discounted cost of the period in which an order placed now (with lead time $\lambda=2$) is first on hand,
--   $$y\;\longmapsto\;\alpha\int_0^\infty\!\!\int_0^\infty L(y-t_1-t_2)\,\varphi(t_1)\varphi(t_2)\,dt_2\,dt_1,$$
--   is a convex function of $y\in\mathbb R$.
--
--   The paper assumes this convexity and remarks that it holds when holding and shortage costs are linear, which is the case of (1); here it is stated as a result. It is what makes the optimal shipment rule of installation 1 a critical-number rule.
--
--   **Formalization Note** Stated for the lead time $\lambda=2$ of the two-installation example, so the prefactor $\alpha^{\lambda-1}$ is $\alpha$.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, p. 478, §2 item 2 (convexity of the one-period costs), with eq. (1) p. 476

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- §2, p. 478, item 2, for the lead time λ = 2: the expected discounted one-period cost
`α ∫₀^∞∫₀^∞ L(y - t₁ - t₂) φ(t₁) φ(t₂) dt₂ dt₁` is a convex function of `y`. -/
theorem L_one_period_convex (M : Model) :
    ConvexOn ℝ univ (fun y : ℝ => M.α * ∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
      M.L (y - t₁ - t₂) * M.φ t₁ * M.φ t₂) := by sorry

end ClarkScarf.Serial
