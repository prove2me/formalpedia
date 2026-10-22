-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_page_of_transverse_hopf
-- name    : BirkhoffGlobalSection.convex_model_page_of_transverse_hopf
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T02:10:19.943744+00:00
-- url     : https://prove2.me/theorems/62e204e6-9fa7-4a63-99bd-59edbd9e681f
-- title:
--   Rational page criterion for a prescribed convex transverse Hopf binding
-- statement:
--   Let $M$ be a convex regularization model, with complete model dynamics $D$. Let $\Gamma$ be a least-period orbit of the model Hamiltonian flow, whose geometric trace equals the image under the coordinate map of an LC periodic orbit $\gamma$. Assume the convex model boundary is centrally symmetric and the radially normalized trace of $\Gamma$ admits an equivariant transverse Hopf isotopy.
--
--   Then
--
--   $$
--   \operatorname{Nonempty}\bigl(\operatorname{ConvexModelRationalPage}(M,D,\gamma)\bigr).
--   $$
--
--   The page conclusion includes smooth immersion and embedding on the closed disk, interior Hamiltonian transversality, exact opposite-boundary antipodal fibers, and returns unbounded in both directions of model time.
--
--   This is the general contact-dynamical criterion for a prescribed Hopf-type binding. It has no geometric retrograde hypothesis. Strict convexity supplies the dynamical-convexity input, and the transverse knot certificate identifies the chosen binding required by the rational disk theorem. Passage to the antipodal quotient must use the radial Reeb flow: the model Hamiltonian itself need not be even. The lift, smooth boundary normalization, and positive change back to model Hamiltonian time belong to this obligation.
--
--   **Formalization Note.** Simplicity, the exact orbit trace, central symmetry, and the transverse isotopy are explicit assumptions, rather than conclusions hidden in a page predicate.
-- source:
--   Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Corollary 1.8 and Section 4, with author correction https://www.mathga.rwth-aachen.de/~hryniewicz/files/elliptic_errata.pdf; Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) (transverse Hopf-fiber clause) and Section 10. This is a coordinate-level specialization to a centrally symmetric strictly convex model, including the explicit lift and model-time transport obligations.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

/-- The rational disk-page criterion for a prescribed transverse Hopf binding
on a centrally symmetric strictly convex Hamiltonian model. The argument must
use the radial Reeb quotient, without assuming that the model Hamiltonian is even. -/
theorem convex_model_page_of_transverse_hopf {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (D : ConvexModelDynamics M φ) (γ : PeriodicOrbit φ)
    (Γ : PeriodicOrbit D.flow)
    (hsimple : IsSimplePeriodicOrbit D.flow Γ)
    (htrace : convexModelOrbitSet Γ = M.toModel '' orbitSet γ)
    (hsymmetric : ∀ y ∈ frontier M.body, -y ∈ frontier M.body)
    (hHopf : Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' convexModelOrbitSet Γ))) :
    Nonempty (ConvexModelRationalPage M D γ) := by sorry

end BirkhoffGlobalSection
