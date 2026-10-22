-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_reeb_transport_of_model_fields
-- name    : BirkhoffGlobalSection.convex_model_sphere_reeb_transport_of_model_fields
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T08:00:15.333717+00:00
-- url     : https://prove2.me/theorems/c4a82d70-fd91-4077-a681-4b8f00468b51
-- title:
--   Radial tangent transport to the weighted sphere Reeb vector
-- statement:
--   For a convex regularization model M and any point u on the Euclidean unit three-sphere, let $a(u)=\operatorname{gauge}_M(u)^{-1}$, $G(u)=a(u)u$, $y=G(u)$ and $X=X_{H_M}(y)$. There exists a sphere tangent vector R such that the weighted primitive $\beta=a^2\alpha$ satisfies $\beta(R)=1$ and $d\beta(R,w)=0$ for every sphere tangent vector w. Its radial image is
--   $$DG_u(R)=\alpha_y(X)^{-1}X.$$
--   The exterior derivative is stated using the actual ambient derivatives of the weighted primitive. Smoothness, radial tangent compatibility, and contact positivity are obtained from the model geometry; no extra lift or sign assumptions are imposed. This is a pointwise statement, not a flow existence theorem.
-- source:
--   Original auxiliary derivation for the Birkhoff global-section formalization. The positive-clock construction uses Mathlib interval integration, inverse derivatives and Flow at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The radial transport uses the accepted platform smooth gauge chart, radial contact pullback, exterior derivative and Hamiltonian normalization results. Not a verbatim source theorem or a prescribed-binding existence result.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Convex.GaugeRescale
open BirkhoffGlobalSection Set
open scoped Topology ContDiff

theorem BirkhoffGlobalSection.convex_model_sphere_reeb_transport_of_model_fields {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (u : Phase) (hu : u ∈ unitThreeSphere) :
    let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
    let G : Phase → Phase := fun x => a x • x
    let y := G u
    let X := hamiltonianVectorField M.modelHamiltonian y
    ∃ R : Phase,
      (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      (a u)^2 * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x R) u w = 0) ∧
      fderiv ℝ G u R = (phaseRadialContact y X)⁻¹ • X := by sorry
