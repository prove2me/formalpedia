-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_geometric_retrograde_page
-- name    : BirkhoffGlobalSection.convex_model_geometric_retrograde_page
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T01:50:30.301758+00:00
-- url     : https://prove2.me/theorems/992c1f88-842a-4156-846e-031662a232f2
-- title:
--   Prescribed geometric retrograde binding in the convex model
-- statement:
--   For physical subcritical parameters, let $M$ be a convex regularization model, let $\varphi$ be a complete antipodally equivariant LC Hamiltonian flow, and let $\delta$ be a geometric Birkhoff retrograde trajectory. Suppose complete model dynamics $D$ identify $\varphi$ with the model Hamiltonian flow through increasing onto clocks.
--
--   Then the image of the closed double lift of $\delta$ bounds a model rational page:
--
--   $$
--   \operatorname{Nonempty}\bigl(\operatorname{ConvexModelRationalPage}(M,D,\widetilde\delta)\bigr).
--   $$
--
--   The page is a smooth immersed embedded closed disk in the convex boundary, transverse in its interior. Opposite boundary parameters are its only antipodal fibers, and every model trajectory outside the binding returns to the disk or its antipode arbitrarily far in both directions of model time.
--
--   This is the remaining contact-topological obligation. It includes identifying the prescribed geometric orbit as a rational unknot of self-linking $-1/2$, obtaining a rational page for the convex quotient, lifting it to the antipodal cover, and arranging a smooth ambient extension and the exact boundary parametrization. It does not assert that arbitrary periodic orbits of convex Hamiltonian systems have this property.
--
--   The conformally symplectic regularization is not assumed to pull back radial contact forms literally. Compatibility of the relevant contact structures, the source's orientation convention, and any passage through the radial Reeb flow must be justified within this theorem.
--
--   **Formalization Note.** Return times are model times. The smooth inverse-coordinate pullback and conversion of returns to LC time are separate proved transport obligations.
-- source:
--   Hryniewicz--Salomao, Elliptic bindings for dynamically convex Reeb flows on the real projective three-space, https://arxiv.org/html/1505.02713v3, Corollary 1.8, Section 1.3.1 (Birkhoff orbit), and Section 4 (two-sided global returns); see the author correction https://www.mathga.rwth-aachen.de/~hryniewicz/files/elliptic_errata.pdf. Liu--Salomao https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) and Section 10. This specialized model-page statement includes explicit identification, lift, and smooth-extension obligations and is not a verbatim theorem in either paper.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

namespace BirkhoffGlobalSection

/-- The prescribed geometric retrograde orbit bounds a rational page in the
convex Hamiltonian model. This includes its contact-topological identification,
the rational disk criterion, lifting, and smooth boundary normalization. -/
theorem convex_model_geometric_retrograde_page
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ)
    (D : ConvexModelDynamics M φ) :
    Nonempty (ConvexModelRationalPage M D
      (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry

end BirkhoffGlobalSection
