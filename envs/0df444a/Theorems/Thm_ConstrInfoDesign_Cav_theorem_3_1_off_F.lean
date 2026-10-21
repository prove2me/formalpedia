-- Prove2me | Theorems.Thm_ConstrInfoDesign_Cav_theorem_3_1_off_F
-- name    : ConstrInfoDesign.Cav.theorem_3_1_off_F
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:18.131964+00:00
-- url     : https://prove2.me/theorems/ccd2f69c-90aa-41a2-a142-5b0dedbf1fb1
-- title:
--   Proof of Theorem 3.1, p. 25 — off the feasibility set F, cav f^ḡ and the value V of CID are both −∞
-- statement:
--   Let $(\mu_0, \gamma) \in \mathbb R^{N+I+E}$ lie outside the feasibility set $\mathcal F$. Then
--   $$\operatorname{cav} f^{\bar g}(\mu_0, \gamma) = -\infty \quad\text{and}\quad V(\mu_0, \gamma) = -\infty.$$
--
--   This is the first step of the proof of Theorem 3.1: it disposes of infeasible parameters, including priors $\mu_0$ outside the simplex, so that the rest of the proof can work on $\mathcal F$.
--
--   **Formalization Note** Both sides are extended reals and $-\infty$ is `⊥`; the value is a supremum over an empty set. The converse (finiteness of cav on $\mathcal F$) is not claimed.
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, p. 25, proof of Theorem 3.1 (first paragraph)

import Mathlib
import Definitions.Def_ConstrInfoDesign_Cav_Model

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- Proof of Theorem 3.1, first step (Doval–Skreta, arXiv:1811.03588v3, p. 25): off the feasibility
set `F`, both the concave hull of `f^ḡ` and the value of (CID) are `−∞`. -/
theorem theorem_3_1_off_F {N nI nE : ℕ} (f : (Fin N → ℝ) → ℝ) (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) (mu0 : Fin N → ℝ) (γI : Fin nI → ℝ) (γE : Fin nE → ℝ) (hF : (mu0, (γI, γE)) ∉ feasibleSet gI gE) : cav (modObj f gI gE) (mu0, (γI, γE)) = ⊥ ∧ value f gI gE mu0 γI γE = ⊥ := by sorry

end ConstrInfoDesign.Cav
