-- Prove2me | Theorems.Thm_DRConvexOpt_Lifting_example_1
-- name    : DRConvexOpt.Lifting.example_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:40.742181+00:00
-- url     : https://prove2.me/theorems/e47995a2-4d78-48a3-84e5-fb7176c00df8
-- title:
--   Example 1 (Mean), pp. 15–16 — the z̃-marginals of {E[ũ] = f, Gz̃ ≼_K ũ a.s.} are exactly the laws with E[Gz̃] ≼_K f
-- statement:
--   Let $G \in \mathbb R^{M \times P}$, $f \in \mathbb R^M$ and let $\mathcal K \subseteq \mathbb R^M$ be a proper cone. Consider the ambiguity set, involving an auxiliary random vector $\tilde u \in \mathbb R^M$,
--   $$
--   \mathcal P = \big\{ \mathbb P \in \mathcal P_0(\mathbb R^P \times \mathbb R^M) : \ \mathbb E_{\mathbb P}[\tilde u] = f,\ \ \mathbb P[G\tilde z \preccurlyeq_{\mathcal K} \tilde u] = 1 \big\}.
--   $$
--   Then
--   $$
--   \Pi_{\tilde z}\mathcal P = \big\{ \mathbb Q \in \mathcal P_0(\mathbb R^P) : \ G\,\mathbb E_{\mathbb Q}[\tilde z] \preccurlyeq_{\mathcal K} f \big\}.
--   $$
--
--   This is the linear case $g(z) = Gz$ of the Lifting Theorem, with no confidence sets: it describes ambiguity sets that impose a conic constraint on the mean of $\tilde z$, as used when only a noisy estimate of the mean is available. The paper also notes $\mathbb Q^0 \in \Pi_{\tilde z}\mathcal P$ for any $\mathbb Q^0$ with $G\,\mathbb E_{\mathbb Q^0}[\tilde z] \preccurlyeq_{\mathcal K} f$, which is immediate from the identity.
--
--   **Formalization Note** The page calls $\mathcal P$ an instance of the standardized ambiguity set (4); as for every set of the form (4), its members are read as having a finite first moment of $(\tilde z, \tilde u)$, and $\mathbb E_{\mathbb Q}[\tilde z]$ is required to exist in the target set. Without the first-moment clause the identity would fail: for $G = 0$ and $f \in \mathcal K$ the lifted set would have $\tilde z$-marginals without a mean. The index set of confidence sets is empty (`nI = 0`).
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 15–16, Example 1 (Mean)

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Example 1 (Mean), pp. 15–16: with g(z) = Gz and no confidence sets, the instance
𝒫 = {P : E_P[ũ] = f, P[Gz̃ ≼_K ũ] = 1} of the ambiguity set (4) has
Π_z̃𝒫 = {Q : G E_Q[z̃] ≼_K f}. As a member of (4), every P ∈ 𝒫 has a finite first moment of (z̃, ũ)
(the integrability convention of (4)); accordingly E_Q[z̃] exists in the target set. -/
theorem example_1 {nP nM : ℕ} (G : Matrix (Fin nM) (Fin nP) ℝ) (f : Fin nM → ℝ)
    (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K) :
    marginal {μ | μ ∈ liftedSet (nI := 0) (fun z => G.mulVec z) f K (fun _ => ∅) (fun _ => 0)
        (fun _ => 0) ∧ Integrable (fun ω => ω) μ} =
      {ν : Measure (Fin nP → ℝ) | IsProbabilityMeasure ν ∧ Integrable (fun z => z) ν ∧
        f - G.mulVec (∫ z, z ∂ν) ∈ K} := by sorry

end DRConvexOpt.Lifting
