-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eq46_optimal_diversion
-- name    : CommonOwnership.Governance.eq46_optimal_diversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:29.861583+00:00
-- url     : https://prove2.me/theorems/a7d6c260-77d3-4492-8840-0c5ae91a649a
-- title:
--   (46), p. 28 (PDF p. 31), with (39), p. 27 — under D(a) = ½φa² the optimal diversion is a* = (1 − (β − s))/φ
-- statement:
--   Let $0<\beta\le1$ and $\varphi\ge1$, and let the deadweight loss be $D(a)=\tfrac12\varphi a^2$. A blockholder who has sold the stake $s\in[0,\beta]$ chooses the diverted fraction $a\in[0,1]$ to maximize
--   $$a+(\beta-s)(1-a)-\tfrac12\varphi a^2 .$$
--   Then the rule
--   $$a^*(s)=\frac{1-(\beta-s)}{\varphi}$$
--   is an optimal diversion rule, and every optimal diversion rule coincides with it on $[0,\beta]$.
--
--   This is the closed form (46) of the first-order condition (39), $D'(a)=1-(\beta-s)$: the smaller the blockholder's residual stake, the more he diverts.
--
--   **Formalization Note** The assumption $\varphi\ge1$ is a disclosed pin that keeps $a^*(s)$ in $[0,1]$ for every $s\in[0,\beta]$ (the paper assumes an interior $a^*$).
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 28 (PDF p. 31), (45), (46); p. 27 (PDF p. 30), (38), (39)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
import Definitions.Def_CommonOwnership_Governance_DiversionModel

namespace CommonOwnership.Governance

/-- (39) and (46), pp. 27–28: under the quadratic deadweight loss (45) with `φ ≥ 1`, the
blockholder's optimal diversion at stake `s ∈ [0, β]` exists, is unique, and equals
`a*(s) = (1 − (β − s))/φ`. -/
theorem eq46_optimal_diversion (β φ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hφ : 1 ≤ φ) :
    IsOptDiversion (divCost φ) β (fun s => (1 - (β - s)) / φ) ∧
      ∀ adiv : ℝ → ℝ, IsOptDiversion (divCost φ) β adiv →
        ∀ s ∈ Set.Icc (0:ℝ) β, adiv s = (1 - (β - s)) / φ := by sorry

end CommonOwnership.Governance
