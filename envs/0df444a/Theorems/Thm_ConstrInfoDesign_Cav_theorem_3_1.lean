-- Prove2me | Theorems.Thm_ConstrInfoDesign_Cav_theorem_3_1
-- name    : ConstrInfoDesign.Cav.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:35.60847+00:00
-- url     : https://prove2.me/theorems/7bc64440-3fa8-4ee7-b80c-30e9205b4948
-- title:
--   Theorem 3.1, p. 7 — the value of constrained information design equals the concave hull of the modified objective f^ḡ at (µ0, γ)
-- statement:
--   Let $f$ and $\bar g = (\bar g_I, \bar g_E)$ be measurable functions on the belief simplex $\Delta(\Omega)$, and let $f^{\bar g}(\mu, \tilde\gamma) = f(\mu) - \delta(\mu, \tilde\gamma \mid C)$ be the modified objective, equal to $f(\mu)$ where the constraints hold pointwise and $-\infty$ elsewhere. For each $(\mu_0, \gamma) \in \mathbb R^{N+I+E}$, the value of the constrained information design problem
--   $$V(\mu_0, \gamma) = \sup_{\tau \in \Delta_{\mu_0}(\Delta(\Omega))} \mathbb E_\tau[f(\mu)] \quad \text{s.t.}\quad \mathbb E_\tau[\bar g_I(\mu)] \ge \gamma_I,\ \ \mathbb E_\tau[\bar g_E(\mu)] = \gamma_E$$
--   coincides with the concave hull of $f^{\bar g}$ at $(\mu_0, \gamma)$:
--   $$V(\mu_0, \gamma) = \operatorname{cav} f^{\bar g}(\mu_0, \gamma).$$
--
--   This is the paper's first main result. Without constraints it reduces to the Kamenica–Gentzkow concavification of $f$ at the prior; with $I + E$ constraints the value is again a concave hull, of a function of $N + I + E$ variables, so a constrained design problem behaves like an unconstrained one with one extra coordinate per constraint.
--
--   **Formalization Note** The statement holds for every $(\mu_0, \gamma)$, including priors outside the simplex and infeasible thresholds, where both sides are $-\infty$. $V$ and cav are extended-real-valued (`EReal`, with $\sup\emptyset = -\infty$). The choice set consists of all Borel probability measures on the simplex with mean $\mu_0$, not only finitely supported ones; $\tau$-integrability of $f$ and of every $\bar g_k$ is required of each admissible $\tau$, since the paper's expectations presuppose it and Lean's integral of a non-integrable function is $0$. No upper semicontinuity is assumed (the paper's Assumptions $f$ and $\bar g$ are not used by Theorem 3.1).
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, p. 7, Theorem 3.1, (3.2)

import Mathlib
import Definitions.Def_ConstrInfoDesign_Cav_Model

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- Theorem 3.1 (Doval–Skreta, arXiv:1811.03588v3, p. 7): for every `(µ0, γ) ∈ ℝ^{N+I+E}`, the value
of (CID) equals the concave hull of the modified objective `f^ḡ` at `(µ0, γ)`:
`V(µ0, γ) = cav f^ḡ(µ0, γ)` (3.2). Both sides are extended reals. -/
theorem theorem_3_1 {N nI nE : ℕ} (f : (Fin N → ℝ) → ℝ) (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) (hf : Measurable f) (hgI : ∀ i, Measurable (gI i)) (hgE : ∀ e, Measurable (gE e)) (mu0 : Fin N → ℝ) (γI : Fin nI → ℝ) (γE : Fin nE → ℝ) : value f gI gE mu0 γI γE = cav (modObj f gI gE) (mu0, (γI, γE)) := by sorry

end ConstrInfoDesign.Cav
