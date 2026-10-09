-- Prove2me | Theorems.Thm_DRConvexOpt_Lifting_proposition_3_2
-- name    : DRConvexOpt.Lifting.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:53.575978+00:00
-- url     : https://prove2.me/theorems/4ff879d4-cfcd-46f6-b16e-5aa2677b1993
-- title:
--   Proposition 3.2 (Mean Absolute Deviation), p. 21 — Π_z̃{E[ũ] = f, ũ ≥ |z̃ − m| a.s.} = {Q : E_Q[|z̃ − m|] ≤ f}
-- statement:
--   Let $m, f \in \mathbb R^P$. Consider the ambiguity set, involving an auxiliary random vector $\tilde u \in \mathbb R^P$,
--   $$
--   \mathcal P = \big\{ \mathbb P \in \mathcal P_0(\mathbb R^P \times \mathbb R^P) : \ \mathbb E_{\mathbb P}[\tilde u] = f,\ \ \mathbb P[\tilde u \ge \tilde z - m,\ \tilde u \ge m - \tilde z] = 1 \big\}.
--   $$
--   Then
--   $$
--   \Pi_{\tilde z}\mathcal P = \big\{ \mathbb Q \in \mathcal P_0(\mathbb R^P) : \ \mathbb E_{\mathbb Q}[|\tilde z - m|] \le f \big\},
--   $$
--   where the absolute value and the inequalities are understood componentwise.
--
--   The right-hand side bounds the marginal mean absolute deviations of $\tilde z$ around $m$, a robust counterpart of the standard deviation; the proposition shows that such bounds fit the paper's standardized ambiguity set.
--
--   **Formalization Note** Expectations are read as existing: $\tilde u$ is required to be integrable in $\mathcal P$, and $|\tilde z - m|$ in the target set. No integrability clause on $\tilde z$ is added to $\mathcal P$, since $0 \le |\tilde z - m| \le \tilde u$ almost surely already forces it. The paper's companion claim $\mathbb Q^0 \in \Pi_{\tilde z}\mathcal P$ for a $\mathbb Q^0$ with $\mathbb E_{\mathbb Q^0}[|\tilde z - m|] \le f$ is immediate from the identity.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 21, Proposition 3, assertion 2 (Mean Absolute Deviation); p. 20 (componentwise absolute value); proof p. 41

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Proposition 3, assertion 2 (Mean Absolute Deviation), p. 21: for m, f ∈ ℝ^P, the lifted set
𝒫 = {P : E_P[ũ] = f, P[ũ ≥ z̃ − m, ũ ≥ m − z̃] = 1} has
Π_z̃𝒫 = {Q : E_Q[|z̃ − m|] ≤ f}; absolute value and ≤ are componentwise. -/
theorem proposition_3_2 {nP : ℕ} (m f : Fin nP → ℝ) :
    marginal {μ : Measure ((Fin nP → ℝ) × (Fin nP → ℝ)) | IsProbabilityMeasure μ ∧
        Integrable (fun ω => ω.2) μ ∧ ∫ ω, ω.2 ∂μ = f ∧
        μ {ω | ω.1 - m ≤ ω.2 ∧ m - ω.1 ≤ ω.2} = 1} =
      {ν : Measure (Fin nP → ℝ) | IsProbabilityMeasure ν ∧ Integrable (fun z => |z - m|) ν ∧
        ∫ z, |z - m| ∂ν ≤ f} := by sorry

end DRConvexOpt.Lifting
