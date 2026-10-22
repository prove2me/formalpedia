-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_sphere_reeb_flow
-- name    : BirkhoffGlobalSection.convex_model_complete_sphere_reeb_flow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T08:11:05.37146+00:00
-- url     : https://prove2.me/theorems/ba41d3da-fd5f-4050-979f-19c1b4f2dda4
-- title:
--   A complete weighted-sphere Reeb flow from convex model dynamics
-- statement:
--   Let M be a convex regularization model and D its supplied complete Hamiltonian dynamics. Set $a(u)=\operatorname{gauge}_M(u)^{-1}$ and $G(u)=a(u)u$. There exist a radial homeomorphism e from the unit three-sphere to the model boundary, a complete continuous normalized boundary flow $\psi$, a complete continuous sphere flow $\theta$, and a vector field R on the sphere.
--
--   The homeomorphism is $e(u)=G(u)$ and its inverse is radial normalization. It conjugates the flows at the same normalized time:
--   $$e(\theta_t(u))=\psi_t(e(u)).$$
--   The boundary velocity is $X_{H_M}/\alpha(X_{H_M})$. Every sphere trajectory has velocity $R(\theta_t(u))$ at every real time. The vector R is sphere tangent and satisfies the Reeb equations for $\beta=a^2\alpha$:
--   $$\beta_u(R(u))=1,\qquad d\beta_u(R(u),w)=0$$
--   for every sphere tangent w. The exterior derivative uses the actual ambient derivatives of the weighted primitive. All positivity and chart requirements follow from the model hypotheses. This theorem assumes M and D; it does not construct them, establish dynamical convexity, or assert a disk-like global surface of section.
-- source:
--   Original auxiliary flow-conjugation and radial tangent argument, reusing the verified convex-model smooth radial chart and the complete normalized-flow and pointwise Reeb-transport results. Uses Mathlib Dynamics/Flow.lean and calculus at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. Not a verbatim theorem of Hryniewicz or a prescribed-binding existence theorem.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Convex.GaugeRescale
open BirkhoffGlobalSection Set
open scoped Topology ContDiff

theorem BirkhoffGlobalSection.convex_model_complete_sphere_reeb_flow {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ) :
    let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
    ∃ e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M,
      ∃ ψ : Flow ℝ (ConvexModelState M),
        ∃ θ : Flow ℝ {u : Phase // u ∈ unitThreeSphere},
          ∃ R : {u : Phase // u ∈ unitThreeSphere} → Phase,
            (∀ u, (e u : Phase) = a u • (u : Phase)) ∧
            (∀ y, (e.symm y : Phase) = radialNormalize (y : Phase)) ∧
            (∀ t u, e (θ t u) = ψ t (e u)) ∧
            (∀ s t, HasDerivAt (fun v => (ψ v s : Phase))
              ((phaseRadialContact (ψ t s)
                (hamiltonianVectorField M.modelHamiltonian (ψ t s)))⁻¹ •
                  hamiltonianVectorField M.modelHamiltonian (ψ t s)) t) ∧
            (∀ u,
              (u.val 0 * R u 0 + u.val 1 * R u 1 + u.val 2 * R u 2 + u.val 3 * R u 3 = 0) ∧
              (a u)^2 * phaseRadialContact u (R u) = 1 ∧
              (∀ w : Phase,
                u.val 0 * w 0 + u.val 1 * w 1 + u.val 2 * w 2 + u.val 3 * w 3 = 0 →
                fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u (R u) -
                  fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x (R u)) u w = 0)) ∧
            (∀ u t, HasDerivAt (fun v => (θ v u : Phase)) (R (θ t u)) t) := by sorry
