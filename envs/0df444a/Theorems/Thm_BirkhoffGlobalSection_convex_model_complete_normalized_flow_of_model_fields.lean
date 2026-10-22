-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields
-- name    : BirkhoffGlobalSection.convex_model_complete_normalized_flow_of_model_fields
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T08:00:08.145507+00:00
-- url     : https://prove2.me/theorems/3b08de00-0d14-4dac-860b-639bb9bf6ab6
-- title:
--   A complete normalized Hamiltonian flow from convex model data
-- statement:
--   Let M be a convex regularization model and D its complete model Hamiltonian dynamics, including the given positive regularization clock relating it to the Levi-Civita flow. There exists a jointly continuous flow on the boundary state space, defined for every real time, whose ambient velocity at every time is
--
--   $$\frac{X_{H_M}(y)}{\alpha_y(X_{H_M}(y))}.$$
--
--   Contact positivity follows from the model hypotheses; it is not an additional assumption. The theorem is conditional on the supplied model and dynamics and does not assert their existence or a global surface of section.
-- source:
--   Original auxiliary derivation for the Birkhoff global-section formalization. The positive-clock construction uses Mathlib interval integration, inverse derivatives and Flow at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The radial transport uses the accepted platform smooth gauge chart, radial contact pullback, exterior derivative and Hamiltonian normalization results. Not a verbatim source theorem or a prescribed-binding existence result.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Convex.GaugeRescale
open BirkhoffGlobalSection Set
open scoped Topology ContDiff

theorem BirkhoffGlobalSection.convex_model_complete_normalized_flow_of_model_fields {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
 :
    ∃ newFlow : Flow ℝ (BirkhoffGlobalSection.ConvexModelState M),
      ∀ s t,
        HasDerivAt (fun v => (newFlow v s : BirkhoffGlobalSection.Phase))
          ((BirkhoffGlobalSection.phaseRadialContact (newFlow t s)
            (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (newFlow t s)))⁻¹ •
              BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (newFlow t s)) t := by sorry
