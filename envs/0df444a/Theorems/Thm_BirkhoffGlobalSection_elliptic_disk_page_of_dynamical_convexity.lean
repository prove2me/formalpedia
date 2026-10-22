-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_elliptic_disk_page_of_dynamical_convexity
-- name    : BirkhoffGlobalSection.elliptic_disk_page_of_dynamical_convexity
-- status  : Open
-- author  : @caleb
-- created : 2026-09-28T03:19:35.7599+00:00
-- url     : https://prove2.me/theorems/a7b9ce80-3e36-4a51-82c0-8e05aaaefa25
-- title:
--   Model rational page from an elliptic disk under dynamical convexity
-- statement:
--   Let $M$ be a convex regularization model with complete model dynamics $D$, and let $\Gamma$ be a simple model periodic orbit whose trace equals the model image of an LC periodic orbit $\gamma$, with centrally symmetric model boundary. Assume the model flow is dynamically convex and that the radially normalized trace of $\Gamma$ bounds a positive elliptic rational disk. Then $\gamma$ carries a convex model rational page: a smooth immersed embedded disk with interior Hamiltonian transversality, exact opposite-boundary antipodal fibers, and returns unbounded in both directions of model time.
--
--   This is the rational open book theorem applied to the disk, followed by the radial Reeb lift, smooth boundary normalization, and the positive change back to model Hamiltonian time. The model Hamiltonian itself is not assumed even; passage to the antipodal quotient uses the radial Reeb flow.
-- source:
--   Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Corollary 1.8 and Section 4; Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) (transverse Hopf-fiber clause) and Section 10. Coordinate-level specialization to a centrally symmetric strictly convex model.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem elliptic_disk_page_of_dynamical_convexity {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (D : ConvexModelDynamics M φ) (γ : PeriodicOrbit φ)
    (Γ : PeriodicOrbit D.flow)
    (hsimple : IsSimplePeriodicOrbit D.flow Γ)
    (htrace : convexModelOrbitSet Γ = M.toModel '' orbitSet γ)
    (hsymmetric : ∀ y ∈ frontier M.body, -y ∈ frontier M.body)
    (hdc : IsDynamicallyConvexOn M.modelHamiltonian (frontier M.body))
    (disk : PositiveEllipticRationalDisk
      (radialNormalize '' convexModelOrbitSet Γ)) :
    Nonempty (ConvexModelRationalPage M D γ) := by sorry

end BirkhoffGlobalSection
