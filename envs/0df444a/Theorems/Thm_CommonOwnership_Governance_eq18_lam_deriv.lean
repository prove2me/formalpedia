-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eq18_lam_deriv
-- name    : CommonOwnership.Governance.eq18_lam_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:48.3872+00:00
-- url     : https://prove2.me/theorems/c0d1ea75-99e9-40d5-99b6-14807f6bea19
-- title:
--   (18), p. 14 (PDF p. 17) — ∂λ/∂s = 2θsβ(β − s)/[(β − s)² + θs²]²
-- statement:
--   Let $\theta>0$ and $\beta>0$, and let $\lambda(s)=\theta s^2/[(\beta-s)^2+\theta s^2]$ be the common-ownership weight (17). Then $\lambda$ is differentiable at every real $s$, with
--   $$\frac{\partial\lambda}{\partial s}=\frac{2\theta s\beta(\beta-s)}{\big[(\beta-s)^2+\theta s^2\big]^2}.$$
--
--   The derivative vanishes at $s=0$ and $s=\beta$ and is positive in between; this is why the softening-of-competition effect vanishes at both ends of the ownership range.
--
--   **Formalization Note** The denominator $(\beta-s)^2+\theta s^2$ is positive for every $s$ because $\theta>0$ and $\beta>0$, so the derivative is stated at every real $s$.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 14 (PDF p. 17), (18); λ from (17), p. 13 (PDF p. 16)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- (18), p. 14: `∂λ/∂s = 2θsβ(β − s) / [(β − s)² + θs²]²`. -/
theorem eq18_lam_deriv (θ β s : ℝ) (hθ : 0 < θ) (hβ : 0 < β) :
    HasDerivAt (fun x => lam θ β x)
      (2 * θ * s * β * (β - s) / ((β - s) ^ 2 + θ * s ^ 2) ^ 2) s := by sorry

end CommonOwnership.Governance
