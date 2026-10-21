-- Prove2me | Theorems.Thm_ConstrInfoDesign_Cav_proposition_A_1
-- name    : ConstrInfoDesign.Cav.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:28.008726+00:00
-- url     : https://prove2.me/theorems/895798d0-662e-4d80-9633-68af5e2dc9b6
-- title:
--   Proposition A.1, p. 24 — finite support is without loss of generality in constrained information design
-- statement:
--   Fix $(\mu_0, \gamma) \in \mathcal F$ and let $\tau \in \Delta_{\mu_0}(\Delta(\Omega))$ satisfy the constraints of CID at $(\mu_0, \gamma)$, with $f$ $\tau$-integrable. Then there is a distribution $\tau^\star \in \Delta_{\mu_0}(\Delta(\Omega))$ with finite support such that $f$ and every $\bar g_k$ are $\tau^\star$-integrable and
--   $$\mathbb E_{\tau^\star}[(f, \bar g)] = \mathbb E_\tau[(f, \bar g)].$$
--   In particular, $\tau^\star$ satisfies the constraints at $(\mu_0, \gamma)$.
--
--   The proposition shows that restricting the choice set of CID to finitely supported distributions does not change its value or its feasibility, which is the bridge between the measure-theoretic program and the finite convex combinations that define the concave hull.
--
--   **Formalization Note** The page states only that $\operatorname{supp}\tau^\star$ is finite and that the expectations agree; "τ⋆ satisfies the constraints" also needs $\tau^\star$ to have mean $\mu_0$, which the proof provides, so the mean $\mu_0$ of $\tau^\star$ is stated explicitly. Integrability of $f$ under $\tau$ is an explicit hypothesis (integrability of the $\bar g_k$ is part of feasibility), because Lean's integral of a non-integrable function is $0$.
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, p. 24, Proposition A.1

import Mathlib
import Definitions.Def_ConstrInfoDesign_Cav_Model

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- Proposition A.1 (Doval–Skreta, arXiv:1811.03588v3, p. 24): finite support is without loss of
generality. For `(µ0, γ) ∈ F` and a feasible `τ` (with `f` integrable), some `τ⋆` with finite
support and mean `µ0` has the same expectations of `f` and of every `ḡ_k`; in particular `τ⋆`
satisfies the constraints. The mean `µ0` of `τ⋆` is stated explicitly (the page leaves it implicit). -/
theorem proposition_A_1 {N nI nE : ℕ} (f : (Fin N → ℝ) → ℝ) (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) (mu0 : Fin N → ℝ) (γI : Fin nI → ℝ) (γE : Fin nE → ℝ) (hF : (mu0, (γI, γE)) ∈ feasibleSet gI gE) (τ : Measure (Fin N → ℝ)) (hτ : IsConstraintFeasible gI gE mu0 γI γE τ) (hf : Integrable f τ) : ∃ τs : Measure (Fin N → ℝ), IsBayesPlausible mu0 τs ∧ τs.support.Finite ∧ Integrable f τs ∧ (∀ i, Integrable (gI i) τs) ∧ (∀ e, Integrable (gE e) τs) ∧ ∫ mu, f mu ∂τs = ∫ mu, f mu ∂τ ∧ (∀ i, ∫ mu, gI i mu ∂τs = ∫ mu, gI i mu ∂τ) ∧ (∀ e, ∫ mu, gE e mu ∂τs = ∫ mu, gE e mu ∂τ) ∧ IsConstraintFeasible gI gE mu0 γI γE τs := by sorry

end ConstrInfoDesign.Cav
